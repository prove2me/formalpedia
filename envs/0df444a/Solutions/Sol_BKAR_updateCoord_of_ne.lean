-- Prove2me | solution 1 for BKAR.updateCoord_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:11:54.51064+00:00
-- url     : https://prove2.me/submissions/2186a5f1-83a4-4a3a-b2da-ba6797edd49d

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pi
import Definitions.Def_BKAR_Interpolation
import Definitions.Def_BKAR_PartialDeriv

set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
namespace BKAR
theorem _root_.solution (x : Edge V → ℝ) {e e' : Edge V} (t : ℝ)
    (hne : e' ≠ e) :
    updateCoord x e t e' = x e' := by
  rw [updateCoord]
  exact Function.update_of_ne hne t x
end BKAR
