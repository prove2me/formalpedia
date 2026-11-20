-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.runLen_inputAt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:37:32.216262+00:00
-- url     : https://prove2.me/submissions/8a492ea8-e098-4e74-8fde-7b38ce9de589

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000

section
-- module Solutions.EditMulticoloring.RamLib2
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
/-!
# Word utilities on `Cmd` (q379, Part L)

Each utility is a counted loop on registers given as parameters; every spec gives the effect,
the frame (registers outside the written list, memory, cursor, output) and a cost bound of the
form `(a * N + b) * kappa B (RAM.bits M)` under a data bound `… ≤ M`.

* `eqW`     — compare two stored blocks (flag register: 1 iff equal);
* `emitW`   — emit a stored block;
* `readW`   — read `N` input symbols, storing `v - 1`;
* `readRun` — the same, also computing the length of the leading non-EOF run (`runLen`);
* `valueW`  — Horner evaluation `V := q * V + a` (`= EditMulticoloring.Code.value`);
* `digitsW` — `D[off + i] := (V / Q ^ i) % Q` for `i < K`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

section Utils
variable (inp : ℕ → ℕ) (B : ℕ)

/-! ### Equality test -/

/-! ### Emitting a stored block -/

/-! ### Reading input -/

/-- If the values are nonzero exactly before position `m`, the run within `k` is `min m k`. -/
theorem runLen_eq_min (g : ℕ → ℕ) (c m : ℕ) (hg : ∀ i, g (c + i) ≠ 0 ↔ i < m) (k : ℕ) :
    runLen g c k = min m k := by
  induction k with
  | zero => simp [runLen]
  | succ k ih =>
    simp only [runLen, ih]
    by_cases hk : k < m
    · rw [if_pos ⟨by omega, (hg k).mpr hk⟩]; omega
    · rw [if_neg (fun h => hk ((hg k).mp h.2))]; omega

/-- The RAM input encodes symbol `a` as `a + 1` and EOF as `0`. -/
theorem inputAt_ne_zero_iff {q : ℕ} (y : Word q) (i : ℕ) : RAM.inputAt y i ≠ 0 ↔ i < y.length := by
  unfold RAM.inputAt
  by_cases h : i < y.length
  · simp [h, List.getElem?_eq_getElem h]
  · have h' : y.length ≤ i := by omega
    simp [h, List.getElem?_eq_none h']

/-! ### Horner evaluation -/

/-! ### Digits -/

theorem runLen_inputAt_oai {q : ℕ} (y : Word q) (c k : ℕ) :
    runLen (RAM.inputAt y) c k = min (y.length - c) k :=
  runLen_eq_min _ c _ (fun i => by rw [inputAt_ne_zero_iff]; omega) k

end Utils

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.runLen_inputAt_oai := @EditMulticoloring.Dev.Ram.runLen_inputAt_oai
