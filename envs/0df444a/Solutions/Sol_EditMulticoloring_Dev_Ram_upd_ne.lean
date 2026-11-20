-- Prove2me | solution 1 for EditMulticoloring.Dev.Ram.upd_ne
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T15:30:32.505237+00:00
-- url     : https://prove2.me/submissions/2a99d931-7589-4459-be95-2e2451068926

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Machine

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

theorem upd_ne_oai {f : ℕ → ℕ} {a b v : ℕ} (h : b ≠ a) : Function.update f a v b = f b :=
  Function.update_of_ne h v f

/-! ## `exec` and `cost` of the constructors -/

/-! ## Monotonicity of the charges -/

/-! ## Syntactic frames -/

/-! ## Loops -/

/-! ## Words stored in arrays -/

/-! ## Copying a block of cells -/

end EditMulticoloring.Dev.Ram
end

theorem solution : type_of% @EditMulticoloring.Dev.Ram.upd_ne_oai := @EditMulticoloring.Dev.Ram.upd_ne_oai
