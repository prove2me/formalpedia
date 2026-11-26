-- Prove2me | solution 1 for Eden.hasDerivAt_squaredRadiusEvolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:09:04.223317+00:00
-- url     : https://prove2.me/submissions/983287fd-3310-45ff-92df-ad6bfe1d36a2

import Definitions.Def_Eden_Algebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Eden_ScalarFlow
import Theorems.Thm_Eden_radialDiscriminant_pos
import Theorems.Thm_Eden_hasDerivAt_squaredRadiusEvolution_of_discriminant_pos

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    HasDerivAt (fun τ => squaredRadiusEvolution τ s)
      (-2 * squaredRadiusEvolution t s * (squaredRadiusEvolution t s - 1) *
        (squaredRadiusEvolution t s - 2)) t :=
  hasDerivAt_squaredRadiusEvolution_of_discriminant_pos (radialDiscriminant_pos ht s)
end Eden
