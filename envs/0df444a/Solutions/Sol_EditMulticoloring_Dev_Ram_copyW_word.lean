-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.copyW_word
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:33:19.223507+00:00
-- url     : https://prove2.me/submissions/17f47ab9-f22b-4a2b-8ca4-e5b5d63edb9e

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000
import Theorems.Thm_EditMulticoloring_Dev_Ram_WordAt_lt
import Theorems.Thm_EditMulticoloring_Dev_Ram_copyW_spec

section
-- module Solutions.EditMulticoloring.RamLib
/-!
# Program-proof library for `Cmd` (q379, Part L)

* `simp` lemmas for `Cmd.exec` / `Cmd.cost` of every constructor and convenience constructor;
* `HS.setR` (register update) and `HS.arr` lemmas;
* syntactic frames: `Cmd.wregs` (registers possibly written), `Cmd.reads`, `Cmd.emits`, `Cmd.stores`;
* monotonicity of `kappa` and `RAM.bits`;
* the general loop lemma `loop_spec`, the counted for-loop `forLoop` with `forLoop_spec`
  (invariant + cost) and its list-fold form `forLoop_fold`;
* `copyW`, a word copy between (array, offset) places.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace EditMulticoloring.Dev.Ram

open EditMulticoloring.Code

/-! ## States -/

/-! ## Small rewriting helpers (use with `simp (disch := omega)`) -/

/-! ## `exec` and `cost` of the constructors -/

/-! ## Monotonicity of the charges -/

/-! ## Syntactic frames -/

/-! ## Loops -/

/-! ## Words stored in arrays -/

/-! ## Copying a block of cells -/

section Copy
variable (inp : ℕ → ℕ) (B : ℕ)

/-- `copyW` moves a stored word. -/
theorem copyW_word_oai {q : ℕ} (S so D dO n j t u one : ℕ) (s : HS) (w : Word q)
    (hreg : [S, so, D, dO, n, j, t, u, one].Nodup) (hSD : s.regs S ≠ s.regs D)
    (hw : WordAt s (s.regs S) (s.regs so) w) (hn : s.regs n = w.length) :
    WordAt ((copyW S so D dO n j t u one).exec inp s) (s.regs D) (s.regs dO) w := by
  have := (copyW_spec inp 0 S so D dO n j t u one s hreg hSD q (s.regs S + s.regs so +
    s.regs D + s.regs dO + s.regs n + q) (fun i hi => ?_) le_rfl).1
  · intro i hi
    rw [this i (by omega), hw i hi]
  · exact (hw.lt i (by omega)).le

end Copy

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.copyW_word_oai := @EditMulticoloring.Dev.Ram.copyW_word_oai
