-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz8.delLower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:34.650961+00:00
-- url     : https://prove2.me/submissions/054e9c3a-f4f2-4edd-a3c3-790e3b3b582f

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
theorem _root_.solution (k f : ℕ) (lb CDel Del : ℝ) (hk : 1 ≤ k) (hf : 1 ≤ f) (hlb : 1 ≤ lb)
    (hC : 4 < CDel) (h : ((k : ℝ) * f * lb) ^ CDel ≤ Del) :
    (k : ℝ) ^ 4 * (f : ℝ) ^ 4 * (k : ℝ) ^ (CDel - 4) ≤ Del := by
  have hk0 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hf0 : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hkpos : (0:ℝ) < k := by linarith
  have hfl : 1 ≤ (f:ℝ) * lb := by nlinarith
  have e1 : ((k : ℝ) * f * lb) ^ CDel = (k:ℝ) ^ CDel * ((f:ℝ) * lb) ^ CDel := by
    rw [mul_assoc, Real.mul_rpow hkpos.le (by positivity)]
  have e2 : (k : ℝ) ^ 4 * (k : ℝ) ^ (CDel - 4) = (k:ℝ) ^ CDel := by
    have : (k:ℝ) ^ (4:ℝ) * (k:ℝ) ^ (CDel - 4) = (k:ℝ) ^ CDel := by
      rw [← Real.rpow_add hkpos]; ring_nf
    rw [← this]; norm_cast
  have e3 : (f:ℝ) ^ 4 ≤ ((f:ℝ) * lb) ^ CDel := by
    calc (f:ℝ) ^ 4 ≤ ((f:ℝ) * lb) ^ 4 := by
          apply pow_le_pow_left₀ (by linarith); nlinarith
      _ = ((f:ℝ) * lb) ^ (4:ℝ) := by norm_cast
      _ ≤ ((f:ℝ) * lb) ^ CDel := Real.rpow_le_rpow_of_exponent_le hfl hC.le
  have hkC : 0 ≤ (k:ℝ) ^ CDel := by positivity
  calc (k : ℝ) ^ 4 * (f : ℝ) ^ 4 * (k : ℝ) ^ (CDel - 4)
      = (k:ℝ) ^ CDel * (f:ℝ) ^ 4 := by rw [← e2]; ring
    _ ≤ (k:ℝ) ^ CDel * ((f:ℝ) * lb) ^ CDel := mul_le_mul_of_nonneg_left e3 hkC
    _ = ((k : ℝ) * f * lb) ^ CDel := e1.symm
    _ ≤ Del := h
end Formalism.FourierDecayAlt.P.Sz8
