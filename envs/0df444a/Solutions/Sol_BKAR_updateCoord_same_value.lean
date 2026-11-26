-- Prove2me | solution 1 for BKAR.updateCoord_same_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:18:03.68258+00:00
-- url     : https://prove2.me/submissions/df57621a-6b93-4f68-8103-94fc21d837ac

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pi
import Definitions.Def_BKAR_Interpolation
import Definitions.Def_BKAR_PartialDeriv

set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
namespace BKAR
theorem _root_.solution (x : Edge V → ℝ) (e : Edge V) :
    updateCoord x e (x e) = x := by
  rw [updateCoord]
  exact Function.update_eq_self e x
end BKAR
