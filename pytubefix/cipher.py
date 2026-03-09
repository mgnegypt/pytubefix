"""
This module contains all the logic needed to find the signature functions.

YouTube's strategy to restrict downloading videos is to send a ciphered version
of the signature to the client, along with the decryption algorithm obfuscated
in JavaScript. For the clients to play the videos, JavaScript must take the
ciphered version, cycle it through a series of "transform functions," and then
signs the media URL with the output.

This module is responsible for (1) finding these "transformations
functions" (2) sends them to be interpreted by nodejs
"""
import json
import logging
import re
import time
from typing import List, Optional, Union

from pytubefix.exceptions import RegexMatchError, InterpretationError
from pytubefix.jsinterp import JSInterpreter, extract_player_js_global_var
from pytubefix.sig_nsig.node_runner import NodeRunner

logger = logging.getLogger(__name__)

MAX_RETRIES = 3
RETRY_DELAY = 0.5

# ─── r values that satisfy common branch conditions like (r>>1&6)>=5 ───
_XOR_BRANCH_R_VALUES = (13, 14, 15, 12, 29, 30, 31, 28)


# ═══════════════════════════════════════════════════════════════
#  Pure helper functions (no state, easily testable)
# ═══════════════════════════════════════════════════════════════

def _extract_function_body(js: str, start: int, max_scan: int = 50_000) -> str:
    """Extract a complete function body by counting balanced braces.

    Starts scanning from *start* (which should point to somewhere
    before or at the opening ``{``) and returns the slice up to
    and including the matching ``}``.
    """
    depth = 0
    limit = min(start + max_scan, len(js))
    for i in range(start, limit):
        ch = js[i]
        if ch == '{':
            depth += 1
        elif ch == '}':
            depth -= 1
            if depth == 0:
                return js[start:i + 1]
    return js[start:limit]


def _find_function_start(js: str, name: str) -> Optional[int]:
    """Return the start offset of a named function definition, or *None*."""
    m = re.search(
        r'(?:function\s+{0}|(?:var\s+)?{0}\s*=\s*function)\s*\('.format(
            re.escape(name)
        ),
        js,
    )
    return m.start() if m else None


def _body_has_try_catch(body: str) -> bool:
    return 'try{' in body or 'try {' in body or 'catch(' in body


def _body_looks_like_nsig(body: str) -> bool:
    """Heuristic: real nsig functions have try/catch, many nulls, and v[a^ refs."""
    return (
        _body_has_try_catch(body)
        and body.count('null') >= 2
        and len(re.findall(r'v\[a\^', body)) > 20
    )


def _is_transient_node_error(exc: Exception) -> bool:
    """True when Node.js returned an empty / unparseable response."""
    if isinstance(exc, json.JSONDecodeError):
        return True
    msg = str(exc)
    return 'Expecting value' in msg and 'char 0' in msg


# ═══════════════════════════════════════════════════════════════
#  Signature pattern registry
# ═══════════════════════════════════════════════════════════════

# Each entry: (compiled_regex, has_dual_params)
# "has_dual_params" means the match contains groups p1 AND p2.

_SIG_PATTERN_SOURCES: list[tuple[str, bool]] = [
    # ── 2025+ obfuscated (TCE / regular player) ──────────────
    (r'(?P<sig>[a-zA-Z0-9$_]+)\((?P<p1>\d+),(?P<p2>\d+),'
     r'(?:[a-zA-Z0-9$_]+\(\d+,\d+,|decodeURIComponent\()'
     r'[a-zA-Z0-9$_.]+\.s\)\)', True),

    (r'(?P<sig>[a-zA-Z0-9$_]+)\((?P<p1>\d+),(?P<p2>\d+),'
     r'(?:[a-zA-Z0-9$_]+\(\d+,\d+,|decodeURIComponent\()'
     r'[a-zA-Z0-9$_]+\)\),[a-zA-Z0-9$_]+\[', True),

    # ── Classic split/join ────────────────────────────────────
    (r'(?P<sig>[a-zA-Z0-9_$]+)\s*=\s*function\(\s*(?P<arg>[a-zA-Z0-9_$]+)\s*\)'
     r'\s*\{\s*(?P=arg)\s*=\s*(?P=arg)\.split\(\s*[a-zA-Z0-9_$\"\[\]]+\s*\)'
     r'\s*;\s*[^}]+;\s*return\s+(?P=arg)\.join\(\s*[a-zA-Z0-9_$\"\[\]]+\s*\)',
     False),

    (r'(?:\b|[^a-zA-Z0-9_$])(?P<sig>[a-zA-Z0-9_$]{2,})\s*=\s*function\(\s*a\s*\)'
     r'\s*\{\s*a\s*=\s*a\.split\(\s*""\s*\)'
     r'(?:;[a-zA-Z0-9_$]{2}\.[a-zA-Z0-9_$]{2}\(a,\d+\))?', False),

    # ── var&&(var=sig(...)) ───────────────────────────────────
    (r'\b(?P<var>[a-zA-Z0-9_$]+)&&\((?P=var)='
     r'(?P<sig>[a-zA-Z0-9_$]{2,})\('
     r'(?:(?P<p1>\d+),decodeURIComponent|decodeURIComponent)'
     r'\((?P=var)\)\)', False),

    # ── Older ─────────────────────────────────────────────────
    (r'\b[cs]\s*&&\s*[adf]\.set\([^,]+\s*,\s*encodeURIComponent'
     r'\s*\(\s*(?P<sig>[a-zA-Z0-9$]+)\(', False),
    (r'\b[a-zA-Z0-9]+\s*&&\s*[a-zA-Z0-9]+\.set\([^,]+\s*,'
     r'\s*encodeURIComponent\s*\(\s*(?P<sig>[a-zA-Z0-9$]+)\(', False),
    (r'\bm=(?P<sig>[a-zA-Z0-9$]{2,})\(decodeURIComponent\(h\.s\)\)', False),

    # ── Obsolete (kept for old player versions) ───────────────
    (r'''("|')signature\1\s*,\s*(?P<sig>[a-zA-Z0-9$]+)\(''', False),
    (r'\.sig\|\|(?P<sig>[a-zA-Z0-9$]+)\(', False),
    (r'yt\.akamaized\.net/\)\s*\|\|\s*.*?\s*[cs]\s*&&\s*[adf]'
     r'\.set\([^,]+\s*,\s*(?:encodeURIComponent\s*\()?\s*'
     r'(?P<sig>[a-zA-Z0-9$]+)\(', False),
    (r'\b[cs]\s*&&\s*[adf]\.set\([^,]+\s*,\s*'
     r'(?P<sig>[a-zA-Z0-9$]+)\(', False),
    (r'\bc\s*&&\s*[a-zA-Z0-9]+\.set\([^,]+\s*,\s*\([^)]*\)\s*\(\s*'
     r'(?P<sig>[a-zA-Z0-9$]+)\(', False),
]

_SIG_PATTERNS = [(re.compile(p), dual) for p, dual in _SIG_PATTERN_SOURCES]


# ═══════════════════════════════════════════════════════════════
#  Nsig call-site parameter extractor
# ═══════════════════════════════════════════════════════════════

_NSIG_CALL_RE = re.compile(
    r'(?<![A-Za-z0-9_$\.])'
    r'(?P<func>{PLACEHOLDER})\s*'          # filled at call-time
    r'\[\w\[\d+\]\]'
    r'\(\s*(?P<a1>[A-Za-z0-9_$]+)'
    r'(?:\s*,\s*(?P<a2>[A-Za-z0-9_$]+))?'
    r'(?:\s*,\s*[^)]*)?'
    r'\s*\)',
    re.MULTILINE,
)


def _extract_nsig_call_params(code: str, func_name: str) -> List[str]:
    """Find control params from call-sites like ``func[Y[6]](this, 1, h)``."""
    pat = re.compile(
        rf'(?<![A-Za-z0-9_$\.])'
        rf'{re.escape(func_name)}\s*'
        r'\[\w\[\d+\]\]'
        r'\(\s*(?P<a1>[A-Za-z0-9_$]+)'
        r'(?:\s*,\s*(?P<a2>[A-Za-z0-9_$]+))?'
        r'(?:\s*,\s*[^)]*)?'
        r'\s*\)',
        re.MULTILINE,
    )
    results = []
    for m in pat.finditer(code):
        # skip "this" and take the actual control value
        chosen = (
            m.group('a2')
            if m.group('a1') == 'this' and m.group('a2')
            else m.group('a1')
        )
        results.append(chosen)
    logger.debug('nsig call params for %s: %s', func_name, results)
    return results


# ═══════════════════════════════════════════════════════════════
#  The Cipher class
# ═══════════════════════════════════════════════════════════════

class Cipher:
    def __init__(self, js: str, js_url: str):
        self.js_url = js_url
        self.js = js

        self._sig_params: Optional[Union[int, List[int]]] = None
        self._nsig_params: Optional[list] = None

        # Detect function names (may populate _sig_params / _nsig_params)
        self.sig_function_name = self._detect_sig_function(js, js_url)
        self.nsig_function_name = self._detect_nsig_function(js, js_url)

        # Boot Node.js runners
        self.runner_sig = self._make_runner(js, self.sig_function_name)
        self.runner_nsig = self._make_runner(js, self.nsig_function_name)

        self.calculated_n: Optional[str] = None
        self.js_interpreter = JSInterpreter(js)

    # ── runner helpers ────────────────────────────────────────

    @staticmethod
    def _make_runner(js: str, func_name: str) -> NodeRunner:
        runner = NodeRunner(js)
        runner.load_function(func_name)
        return runner

    def _reload_runner(self, runner: NodeRunner, label: str) -> None:
        """Try to revive a runner after a transient failure."""
        try:
            func = (
                self.nsig_function_name if 'nsig' in label
                else self.sig_function_name
            )
            runner.load_function(func)
        except Exception:
            pass

    # ── retry infrastructure ─────────────────────────────────

    def _call_with_retry(
        self, runner: NodeRunner, args: list, label: str = "call"
    ):
        """Call *runner* with automatic retry on transient Node.js errors."""
        last_exc: Optional[Exception] = None
        for attempt in range(1, MAX_RETRIES + 1):
            try:
                return runner.call(args)
            except Exception as exc:
                if _is_transient_node_error(exc) and attempt < MAX_RETRIES:
                    delay = RETRY_DELAY * attempt
                    logger.warning(
                        '%s: transient error (attempt %d/%d), '
                        'retrying in %.1fs …',
                        label, attempt, MAX_RETRIES, delay,
                    )
                    last_exc = exc
                    time.sleep(delay)
                    self._reload_runner(runner, label)
                    continue
                raise
        raise last_exc  # type: ignore[misc]

    # ── argument building ────────────────────────────────────

    @staticmethod
    def _build_call_args(
        params: Optional[Union[int, list]], value: str
    ) -> list:
        """Prepend params (if any) to the actual value."""
        if params is None:
            return [value]
        if isinstance(params, list):
            return [*params, value]
        return [params, value]

    # ════════════════════════════════════════════════════════════
    #  Public API
    # ════════════════════════════════════════════════════════════

    def get_sig(self, ciphered_signature: str) -> str:
        """Decode the stream signature to prevent 403 errors.

        :param ciphered_signature: The raw signature from YouTube.
        :returns: Decoded signature string.
        :raises InterpretationError: If decoding fails.
        """
        args = self._build_call_args(self._sig_params, ciphered_signature)
        try:
            sig = self._call_with_retry(self.runner_sig, args, 'sig')
        except Exception as exc:
            raise InterpretationError(js_url=self.js_url, reason=exc)

        if not isinstance(sig, str) or 'error' in sig:
            raise InterpretationError(js_url=self.js_url, reason=sig)
        return sig

    def get_nsig(self, n: str) -> str:
        """Transform the throttling parameter *n* to prevent 403 errors.

        :param n: The raw ``n`` parameter value.
        :returns: Transformed ``n`` string.
        :raises InterpretationError: If transformation fails.
        """
        try:
            nsig = self._try_nsig_variants(n)
        except InterpretationError:
            raise
        except Exception as exc:
            raise InterpretationError(js_url=self.js_url, reason=exc)

        if not isinstance(nsig, str) or 'error' in nsig or '_w8_' in nsig:
            raise InterpretationError(js_url=self.js_url, reason=nsig)
        return nsig

    def _try_nsig_variants(self, n: str):
        """Iterate over parameter variants and return the first good nsig."""
        if not self._nsig_params:
            return self._call_with_retry(self.runner_nsig, [n], 'nsig')

        last_nsig = None
        for param in self._nsig_params:
            args = [*param, n] if isinstance(param, list) else [param, n]
            nsig = self._call_with_retry(self.runner_nsig, args, 'nsig')
            if (
                isinstance(nsig, str)
                and 'error' not in nsig
                and '_w8_' not in nsig
            ):
                return nsig
            last_nsig = nsig
        return last_nsig

    # ════════════════════════════════════════════════════════════
    #  Signature function detection
    # ════════════════════════════════════════════════════════════

    def _detect_sig_function(self, js: str, js_url: str) -> str:
        logger.debug('Detecting signature cipher function')
        for compiled_re, has_dual in _SIG_PATTERNS:
            m = compiled_re.search(js)
            if not m:
                continue

            sig_name = m.group('sig')
            groups = m.groupdict()

            if has_dual and groups.get('p2'):
                self._sig_params = [int(groups['p1']), int(groups['p2'])]
            elif groups.get('p1'):
                self._sig_params = int(groups['p1'])

            logger.debug('sig function: %s  (params=%s)', sig_name, self._sig_params)
            return sig_name

        raise RegexMatchError(
            caller='get_sig_function_name',
            pattern=f'multiple in {js_url}',
        )

    # ════════════════════════════════════════════════════════════
    #  N-signature function detection  (strategy chain)
    # ════════════════════════════════════════════════════════════

    def _detect_nsig_function(self, js: str, js_url: str) -> str:
        logger.debug('Detecting nsig function')

        # Strategies ordered by reliability — first match wins
        for strategy in (
            self._nsig_via_w8_sentinel,
            self._nsig_via_short_var,
            self._nsig_via_xor_branch,
            self._nsig_via_broad_var,
        ):
            name = strategy(js)
            if name:
                return name

        raise RegexMatchError(
            caller='get_nsig_function_name',
            pattern=f'multiple in {js_url}',
        )

    # ── strategy 1: _w8_ sentinel in global array ────────────

    def _nsig_via_w8_sentinel(self, js: str) -> Optional[str]:
        global_obj, varname, code = extract_player_js_global_var(js)
        if not (global_obj and varname and code):
            return None

        logger.debug('Global array var: %s', varname)
        global_obj = JSInterpreter(js).interpret_expression(code, {}, 100)

        for idx, val in enumerate(global_obj):
            if not str(val).endswith('_w8_'):
                continue
            logger.debug('_w8_ at index %d', idx)

            esc_var, esc_idx = re.escape(varname), idx

            _W8_PATTERNS = [
                # Strict: catch block references varname[idx]+argname
                rf'''(?xs)
                    [;\n](?:(?P<f>function\s+)|(?:var\s+)?)
                    (?P<funcname>[a-zA-Z0-9_$]+)\s*(?(f)|=\s*function\s*)
                    \(\s*(?:[a-zA-Z0-9_$]+\s*,\s*)?
                    (?P<argname>[a-zA-Z0-9_$]+)
                    (?:\s*,\s*[a-zA-Z0-9_$]+)*\s*\)\s*\{{
                    (?:(?!(?<!\{{)\}};(?![\]\)])).)*
                    \}}\s*catch\(\s*[a-zA-Z0-9_$]+\s*\)\s*
                    \{{\s*(?:return\s+|[\w=]+){esc_var}\[{esc_idx}\]\s*\+\s*
                    (?P=argname)\s*[\}};]
                    .*?\s*return\s+[^}}]+\}}[;\n]
                ''',
                # Relaxed: any function referencing varname[idx]
                rf'''(?xs)
                    [;\n](?:(?P<f>function\s+)|(?:var\s+)?)
                    (?P<funcname>[a-zA-Z0-9_$]+)\s*(?(f)|=\s*function\s*)
                    \([^)]*\)\s*\{{
                    (?:(?!(?<!\{{)\}};).)*?
                    {esc_var}\[{esc_idx}\]
                    (?:(?!(?<!\{{)\}};).)*?
                    \}}[;\n]
                ''',
            ]
            for pat in _W8_PATTERNS:
                m = re.search(pat, js)
                if m:
                    name = m.group('funcname')
                    logger.debug('nsig (_w8_): %s', name)
                    self._nsig_params = _extract_nsig_call_params(js, name)
                    return name
        return None

    # ── strategy 2: short variable assignment ─────────────────

    @staticmethod
    def _nsig_via_short_var(js: str) -> Optional[str]:
        m = re.search(
            r'var\s+[a-zA-Z0-9$_]{2,3}\s*=\s*\[(?P<fn>[a-zA-Z0-9$_]{2,})\]',
            js,
        )
        if m:
            name = m.group('fn')
            logger.debug('nsig (short-var): %s', name)
            return name
        return None

    # ── strategy 3: XOR multi-branch (2025+) ─────────────────

    def _nsig_via_xor_branch(self, js: str) -> Optional[str]:
        xor_re = re.compile(
            r'([a-zA-Z0-9_$]+)\s*=\s*function\s*'
            r'\(r\s*,\s*p\s*,\s*I(?:\s*,\s*S)?\)\s*\{'
            r'var\s+a\s*=\s*p\s*\^\s*r\b'
        )
        for fm in xor_re.finditer(js):
            candidate = fm.group(1)
            chunk = js[fm.start():fm.start() + 500]

            recursive = re.search(
                rf'{re.escape(candidate)}\(a\^(\d+)\s*,\s*a\^(\d+)\s*,',
                chunk,
            )
            if not recursive:
                continue

            body = _extract_function_body(js, fm.start())
            if not _body_looks_like_nsig(body):
                continue

            c1, c2 = int(recursive.group(1)), int(recursive.group(2))
            a_val = c1 ^ c2

            self._nsig_params = [
                [r_val, a_val ^ r_val] for r_val in _XOR_BRANCH_R_VALUES
            ]

            logger.debug(
                'nsig (XOR): %s  c1=%d c2=%d a=%d',
                candidate, c1, c2, a_val,
            )
            return candidate
        return None

    # ── strategy 4: broad var=[func] with body validation ────

    def _nsig_via_broad_var(self, js: str) -> Optional[str]:
        for m in re.finditer(
            r'var\s+[a-zA-Z0-9$_]+\s*=\s*\[(?P<fn>[a-zA-Z0-9$_]+)\]',
            js,
        ):
            candidate = m.group('fn')
            start = _find_function_start(js, candidate)
            if start is None:
                continue

            body = _extract_function_body(js, start)
            if len(body) < 200:
                continue

            if _body_has_try_catch(body):
                logger.debug('nsig (broad-var): %s', candidate)
                self._nsig_params = _extract_nsig_call_params(js, candidate)
                return candidate
        return None
