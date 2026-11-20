-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.valueW_word
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:37:34.884554+00:00
-- url     : https://prove2.me/submissions/a5ea8215-4556-471d-8f61-27098c963a19

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_lt
import Theorems.Thm_EditMulticoloring_Dev_Ram_valueW_spec

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

/-! ### Horner evaluation -/

theorem horner_value {q : ℕ} (w : Word q) (g : ℕ → ℕ) (hg : ∀ i (h : i < w.length), g i = (w[i]).val) :
    horner q g w.length = value w := by
  have key : ∀ k ≤ w.length, horner q g k = (w.take k).foldl (fun a b => q * a + b.val) 0 := by
    intro k hk
    induction k with
    | zero => simp [horner]
    | succ k ih =>
      have ht : w.take (k + 1) = w.take k ++ [w[k]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (show k < w.length by omega)]; rfl
      rw [horner, ih (by omega), ht, List.foldl_append]
      simp [hg k (by omega)]
  rw [key _ le_rfl, List.take_length]; rfl

/-! ### Digits -/

/-- `valueW` on a stored word computes `EditMulticoloring.Code.value`. -/
theorem valueW_word_oai {q : ℕ} (r : ℕ) (s : HS) (w : Word q) (hw : WordAt s (s.regs r) (s.regs (r + 1)) w)
    (hn : s.regs (r + 2) = w.length) (hq : s.regs (r + 3) = q) :
    ((valueW r).exec inp s).regs (r + 4) = value w := by
  have := (valueW_spec inp 0 r s _ (fun i hi => by rw [hq]; exact hw.lt i (by omega)) le_rfl).1
  rw [this, hn, hq]
  exact horner_value w _ (fun i h => hw i h)

end Utils

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.valueW_word_oai := @EditMulticoloring.Dev.Ram.valueW_word_oai
