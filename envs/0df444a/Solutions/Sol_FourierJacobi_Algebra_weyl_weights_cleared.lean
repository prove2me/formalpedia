-- Prove2me | solution 1 for FourierJacobi.Algebra.weyl_weights_cleared
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:18:56.972123+00:00
-- url     : https://prove2.me/submissions/98c8a006-195c-4f0e-aab9-80b5246d26e4

import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Algebra_WeylEvaluation

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
namespace FourierJacobi.Algebra
theorem _root_.solution (t a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0)
    (hab₁ : a * b - 1 ≠ 0) (i : Fin 8) :
    weylWall a b * weylWeights t a b i = weylWeightNumerators t a b i := by
  have ha₁' : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp ha₁))
  have hb₁' : 1 - b ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hb₁))
  have hab' : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hab))
  have hab₁' : 1 - a * b ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hab₁))
  fin_cases i <;>
    simp [weylWall, weylWeights, weylWeightNumerators, rootFactor] <;>
    field_simp <;> ring
end FourierJacobi.Algebra
