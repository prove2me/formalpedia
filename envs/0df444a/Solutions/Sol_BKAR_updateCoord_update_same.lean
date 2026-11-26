-- Prove2me | solution 1 for BKAR.updateCoord_update_same
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:17:49.375929+00:00
-- url     : https://prove2.me/submissions/b123b5e2-bcab-4a51-8ed1-1b3536559859

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pi
import Definitions.Def_BKAR_Interpolation
import Definitions.Def_BKAR_PartialDeriv

set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
namespace BKAR
theorem _root_.solution (x : Edge V → ℝ) (e : Edge V)
    (s t : ℝ) :
    updateCoord (updateCoord x e s) e t = updateCoord x e t := by
  rw [updateCoord, updateCoord]
  exact Function.update_idem s t x
end BKAR
