-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz8.quantOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:39.964576+00:00
-- url     : https://prove2.me/submissions/c7bc3489-86f9-4808-b417-9d4aa109588a

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmRingIdempotentUnitRatioIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.Sz Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.Sz8
namespace Formalism.FourierDecayAlt.P.Sz8
theorem _root_.solution (x fr mr K P W Del : ℝ) (hx : 1 ≤ x) (hm : 0 < mr) (hmf : mr ≤ fr) (hf : 1 ≤ fr)
    (hPK : P ^ 2 ≤ K) (hW : 0 < W) (hWx : 1000 * W ^ 2 ≤ x)
    (hDel : x ^ 4 * fr ^ 4 * K ≤ Del) :
    P ≤ Real.sqrt (Del / (x * (10 * mr) ^ 3)) / W := by
  have hx0 : 0 < x := by linarith
  rcases le_or_gt P 0 with hP | hP
  · have : 0 ≤ Real.sqrt (Del / (x * (10 * mr) ^ 3)) / W := by positivity
    linarith
  rw [le_div_iff₀ hW]
  apply Real.le_sqrt_of_sq_le
  rw [le_div_iff₀ (by positivity)]
  have hK : 0 ≤ K := le_trans (sq_nonneg P) hPK
  have hm3 : mr ^ 3 ≤ fr ^ 4 := by
    calc mr ^ 3 ≤ fr ^ 3 := pow_le_pow_left₀ hm.le hmf 3
      _ ≤ fr ^ 4 := pow_le_pow_right₀ hf (by norm_num)
  have hx3 : x ≤ x ^ 3 := by
    calc x = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ 3 := pow_le_pow_right₀ hx (by norm_num)
  have A1 : (P * W) ^ 2 * (x * (10 * mr) ^ 3) = P ^ 2 * (1000 * W ^ 2) * x * mr ^ 3 := by ring
  rw [A1]
  have B1 : P ^ 2 * (1000 * W ^ 2) * x * mr ^ 3 ≤ P ^ 2 * x * x * fr ^ 4 := by
    have := mul_le_mul hWx hm3 (by positivity) hx0.le
    have hp2 : 0 ≤ P ^ 2 := sq_nonneg P
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hp2 hx0.le)]
  have B2 : P ^ 2 * x * x * fr ^ 4 ≤ x ^ 4 * fr ^ 4 * K := by
    have hxx : x * x ≤ x ^ 4 := by nlinarith
    have : P ^ 2 * (x * x) * fr ^ 4 ≤ K * x ^ 4 * fr ^ 4 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul hPK hxx (by positivity) hK
    nlinarith
  linarith
end Formalism.FourierDecayAlt.P.Sz8
