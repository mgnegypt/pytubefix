"""
Smart Cipher Module for YouTube Signature Decryption.
Utilizes dynamic execution (V8 via PyMiniRacer if available) and 
Heuristic structural matching to bypass heavy obfuscation.
"""
import logging
import re
import time
import json

from pytubefix.exceptions import RegexMatchError, InterpretationError
from pytubefix.jsinterp import JSInterpreter, extract_player_js_global_var

# Try to load the V8 Engine for native execution (The Genius Approach)
# If not installed, it falls back to the standard NodeRunner
try:
    from py_mini_racer import MiniRacer
    HAS_V8 = True
except ImportError:
    from pytubefix.sig_nsig.node_runner import NodeRunner
    HAS_V8 = False

MAX_RETRIES = 3
RETRY_DELAY = 0.5

logger = logging.getLogger(__name__)


class Cipher:
    def __init__(self, js: str, js_url: str):
        self.js_url = js_url
        self.js = self._sanitize_js(js)
        
        self._sig_param_val = None
        self._nsig_param_val = None
        
        self.sig_function_name = self.get_sig_function_name(self.js, js_url)
        self.nsig_function_name = self.get_nsig_function_name(self.js, js_url)

        # Initialize the Execution Environment
        self.v8_ctx = None
        self.runner_sig = None
        self.runner_nsig = None
        
        self._setup_execution_environment()

        self.calculated_n = None
        self.js_interpreter = JSInterpreter(self.js)

    def _sanitize_js(self, js: str) -> str:
        """Clean the JS from potential execution blockers before evaluating."""
        # Remove DOM-dependent code that crashes headless JS engines
        js = re.sub(r'document\.[^;]+;', '', js)
        js = re.sub(r'window\.[^;]+;', '', js)
        return js

    def _setup_execution_environment(self):
        """Sets up the smartest available JS execution environment."""
        if HAS_V8:
            logger.debug("Using PyMiniRacer (V8) for lightning-fast execution.")
            self.v8_ctx = MiniRacer()
            # Load the entire JS context once
            self.v8_ctx.eval(self.js)
        else:
            logger.debug("PyMiniRacer not found. Falling back to NodeRunner.")
            self.runner_sig = NodeRunner(self.js)
            self.runner_sig.load_function(self.sig_function_name)
            self.runner_nsig = NodeRunner(self.js)
            self.runner_nsig.load_function(self.nsig_function_name)

    def _execute_js(self, func_name: str, args: list, runner_fallback, label="call"):
        """Executes JS using V8 if available, otherwise safely retries via NodeRunner."""
        if HAS_V8:
            try:
                # Direct V8 execution - extremely fast and stable
                return self.v8_ctx.call(func_name, *args)
            except Exception as e:
                logger.error(f"V8 Execution failed for {label}: {e}")
                raise InterpretationError(js_url=self.js_url, reason=e)
        
        # Fallback to NodeRunner with the retry logic from cipher_new.py
        last_exc = None
        for attempt in range(1, MAX_RETRIES + 1):
            try:
                return runner_fallback.call(args)
            except Exception as e:
                if attempt < MAX_RETRIES:
                    logger.warning(f"{label}: Engine error attempt {attempt}/{MAX_RETRIES}, retrying...")
                    last_exc = e
                    time.sleep(RETRY_DELAY * attempt)
                    try:
                        runner_fallback.load_function(func_name)
                    except Exception:
                        pass
                    continue
                raise last_exc

    def get_nsig(self, n: str):
        """Interpret the function that transforms the signature parameter `n`."""
        try:
            if self._nsig_param_val:
                nsig = None
                for param in self._nsig_param_val:
                    args = [*param, n] if isinstance(param, list) else [param, n]
                    nsig = self._execute_js(self.nsig_function_name, args, self.runner_nsig, "nsig")
                    if isinstance(nsig, str) and 'error' not in nsig and '_w8_' not in nsig:
                        break
            else:
                nsig = self._execute_js(self.nsig_function_name, [n], self.runner_nsig, "nsig")
        except Exception as e:
            raise InterpretationError(js_url=self.js_url, reason=e)

        if not nsig or 'error' in nsig or '_w8_' in nsig or not isinstance(nsig, str):
            raise InterpretationError(js_url=self.js_url, reason=nsig)
        return nsig

    def get_sig(self, ciphered_signature: str) -> str:
        """Interprets the function that signs the streams."""
        try:
            if self._sig_param_val:
                args = [*self._sig_param_val, ciphered_signature] if isinstance(self._sig_param_val, list) else [self._sig_param_val, ciphered_signature]
                sig = self._execute_js(self.sig_function_name, args, self.runner_sig, "sig")
            else:
                sig = self._execute_js(self.sig_function_name, [ciphered_signature], self.runner_sig, "sig")
        except Exception as e:
            raise InterpretationError(js_url=self.js_url, reason=e)

        if not sig or 'error' in sig or not isinstance(sig, str):
            raise InterpretationError(js_url=self.js_url, reason=sig)
        return sig

    def get_sig_function_name(self, js: str, js_url: str) -> str:
        """Extract the signature function using Heuristic Matching."""
        logger.debug("Using Heuristic search for signature cipher name")
        
        # Smart Structural Pattern: Looks for the actual logic (split -> transform -> join)
        # rather than guessing variable names.
        structural_pattern = re.compile(
            r'(?P<sig>[a-zA-Z0-9$_]+)\s*=\s*function\(\s*(?P<arg>[a-zA-Z0-9$_]+)\s*\)\s*\{'
            r'\s*(?P=arg)\s*=\s*(?P=arg)\.split\([^}]+\.join\('
        )
        
        match = structural_pattern.search(js)
        if match:
            return match.group('sig')

        # Fallback to the known patterns if structural search fails
        patterns = [
            r'(?P<sig>[a-zA-Z0-9$_]+)\((?P<param>\d+),(?P<param2>\d+),(?:[a-zA-Z0-9$_]+\(\d+,\d+,|decodeURIComponent\()[a-zA-Z0-9$_.]+\.s\)\)',
            r'\b(?P<var>[a-zA-Z0-9_$]+)&&\((?P=var)=(?P<sig>[a-zA-Z0-9_$]{2,})\((?:(?P<param>\d+),decodeURIComponent|decodeURIComponent)\((?P=var)\)\)',
        ]
        
        for pattern in patterns:
            m = re.search(pattern, js)
            if m:
                groups = m.groupdict()
                if "param2" in groups and groups.get("param2"):
                    self._sig_param_val = [int(groups['param']), int(groups['param2'])]
                elif "param" in groups and groups.get("param"):
                    self._sig_param_val = int(groups['param'])
                return groups['sig']

        raise RegexMatchError(caller="get_sig_function_name", pattern=f"Heuristic failed in {js_url}")

    def get_nsig_function_name(self, js: str, js_url: str):
        """Extract the nsig function using Multi-Strategy Heuristics."""
        logger.debug("Using Heuristic search for nsig name")
        
        # Strategy 1: XOR Branching structural detection (Highest priority for modern YT)
        xor_pattern = re.compile(r'([a-zA-Z0-9_$]+)\s*=\s*function\s*\(r\s*,\s*p\s*,\s*I(?:\s*,\s*S)?\)\s*\{\s*var\s+a\s*=\s*p\s*\^\s*r\b')
        for match in xor_pattern.finditer(js):
            candidate = match.group(1)
            func_start = match.start()
            chunk = js[func_start:func_start + 1000]
            
            # Validate it's the right function by looking for recursive constants
            recursive = re.search(rf'{re.escape(candidate)}\(a\^(\d+)\s*,\s*a\^(\d+)\s*,', chunk)
            if recursive and 'try' in chunk and 'catch' in chunk:
                c1, c2 = int(recursive.group(1)), int(recursive.group(2))
                a_val = c1 ^ c2
                self._nsig_param_val = [[r, a_val ^ r] for r in [13, 14, 15, 12, 29, 30, 31, 28]]
                return candidate

        # Strategy 2: Global Array Injection (_w8_)
        try:
            global_obj, varname, code = extract_player_js_global_var(js)
            if global_obj and varname:
                # Instead of interpreting manually, we construct a quick regex block
                obj_block = re.search(rf'var\s+{re.escape(varname)}\s*=\s*\[(.*?)\];', js, re.DOTALL)
                if obj_block:
                    elements = obj_block.group(1).split(',')
                    for k, val in enumerate(elements):
                        if '_w8_' in val:
                            nsig_structural = re.search(rf'([a-zA-Z0-9_$]+)\s*=\s*function\([^)]*\)\s*\{{[^}}]*?{re.escape(varname)}\[{k}\]', js)
                            if nsig_structural:
                                candidate = nsig_structural.group(1)
                                self._nsig_param_val = self._extract_nsig_param_val(js, candidate)
                                return candidate
        except Exception as e:
            logger.debug(f"Global array strategy failed gracefully: {e}")

        # Strategy 3: Fast array var initialization
        match = re.search(r"var\s*[a-zA-Z0-9$_]{2,3}\s*=\s*\[(?P<funcname>[a-zA-Z0-9$_]{2,})\]", js)
        if match:
            return match.group("funcname")

        raise RegexMatchError(caller="get_nsig_function_name", pattern=f"All strategies failed in {js_url}")

    @staticmethod
    def _extract_nsig_param_val(code: str, func_name: str) -> list:
        pattern = re.compile(
            rf'(?<![A-Za-z0-9_$\.])(?P<func>{re.escape(func_name)})\s*\[\w\[\d+\]\]\(\s*(?P<arg1>[A-Za-z0-9_$]+)(?:\s*,\s*(?P<arg2>[A-Za-z0-9_$]+))?',
            re.MULTILINE
        )
        return [m.group('arg2') if m.group('arg1') == 'this' and m.group('arg2') else m.group('arg1') for m in pattern.finditer(code)]


