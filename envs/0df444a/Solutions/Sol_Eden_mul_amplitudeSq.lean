-- Prove2me | solution 1 for Eden.mul_amplitudeSq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:03:39.905786+00:00
-- url     : https://prove2.me/submissions/a252de3b-8558-40b5-8b2d-ca1ef57900ff

import Definitions.Def_Eden_Algebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Eden_ScalarFlow
import Theorems.Thm_Eden_radialDiscriminant_pos
import Theorems.Thm_Eden_mul_amplitudeSq_of_discriminant_pos

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    s * amplitudeSq t s = squaredRadiusEvolution t s :=
  mul_amplitudeSq_of_discriminant_pos (radialDiscriminant_pos ht s)
end Eden
