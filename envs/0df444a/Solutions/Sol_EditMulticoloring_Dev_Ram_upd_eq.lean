-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.upd_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:30:57.911929+00:00
-- url     : https://prove2.me/submissions/002a61e9-dd39-4c7c-844a-6710d6f59d9e

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Machine
import Definitions.Def_EMRamB000

section
-- module Solutions.EditMulticoloring.RamLib
attribute [-simp] _root_.EditMulticoloring.Dev.Ram.arith_xor
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

theorem upd_eq_oai {f : ℕ → ℕ} {a b v : ℕ} (h : b = a) : Function.update f a v b = v := by
  subst h; simp

/-! ## `exec` and `cost` of the constructors -/

/-! ## Monotonicity of the charges -/

/-! ## Syntactic frames -/

/-! ## Loops -/

/-! ## Words stored in arrays -/

/-! ## Copying a block of cells -/

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.upd_eq_oai := @EditMulticoloring.Dev.Ram.upd_eq_oai
