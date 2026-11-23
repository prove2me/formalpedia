-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz9.small_f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:18.070887+00:00
-- url     : https://prove2.me/submissions/acec95bb-17de-4b47-a52d-662d4eaeff10

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaBoundOnBoundary
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmRingIdempotentUnitRatioIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SixteenMulLeTwoPow
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz9_sixteen_mul_le_two_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz9
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz9
theorem _root_.solution (f k : ℕ) (hfk : f ≤ k) (hk : 7 ≤ k) : (f : ℝ) * (8 / 2 ^ k) ≤ Real.log 2 := by
  have h1 := sixteen_mul_le_two_pow k hk
  have h2 : (k : ℝ) * 16 ≤ (2 : ℝ) ^ k := by exact_mod_cast h1
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have hf : (f : ℝ) ≤ k := by exact_mod_cast hfk
  have hlog := Real.log_two_gt_d9
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith [mul_lt_mul_of_pos_right hlog hpos]
end Formalism.FourierDecayAlt.P.Sz9
