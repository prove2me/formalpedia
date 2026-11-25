-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.corner_relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:37:23.238795+00:00
-- url     : https://prove2.me/submissions/3c5652c8-74be-4c59-b7a6-bf10c3ad0bdb

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G6_isStrictUpper_strictUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G6_isStrictUpper_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_G6_pow_card_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G6
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.CornerRelation := by
  intro n t c a b v
  have hN : (-(strictUpper v)) ^ n = 0 :=
    pow_card_eq_zero (isStrictUpper_neg (isStrictUpper_strictUpper v))
  have key : ∀ j ∈ Finset.range n,
      (rhoOf t a v ⬝ᵥ ((-(Xof t v)) ^ j *ᵥ (t • b))) * t ^ (n - 1 - j) =
        t ^ n * (a ⬝ᵥ ((wMat n * ((1 - -(strictUpper v)) * (-(strictUpper v)) ^ j)) *ᵥ (t • b))) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have e1 : -(Xof t v) = t • (-(strictUpper v)) := by simp [Xof]
    have e2 : t ^ n = t * t ^ j * t ^ (n - 1 - j) := by
      rw [← pow_succ', ← pow_add]; congr 1; omega
    rw [e1, smul_pow, rhoOf, Formalism.FourierDecayAlt.G.upper, sub_neg_eq_add, Matrix.smul_mulVec, smul_dotProduct,
      dotProduct_smul, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, e2, smul_eq_mul, smul_eq_mul,
      Matrix.mul_assoc]
    ring
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, ← dotProduct_sum, ← Matrix.sum_mulVec,
    ← Finset.mul_sum, ← Finset.mul_sum, mul_neg_geom_sum, hN, sub_zero, mul_one]
  ring
end Formalism.FourierDecayAlt.P
