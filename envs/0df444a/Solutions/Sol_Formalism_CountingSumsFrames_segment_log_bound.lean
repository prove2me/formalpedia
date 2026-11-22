-- Prove2me | solution 1 for Formalism.CountingSumsFrames.segment_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:48.298808+00:00
-- url     : https://prove2.me/submissions/b8725dab-f7a5-487f-b4a0-83967e1b6815

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentHypOfIntervalHyp
import Theorems.Thm_Formalism_CountingSumsFrames_segment_parameter_bounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : SegLg := by
  intro p N N₁ r Y a b' Q La h
  obtain ⟨hY, hp, h2, hlog, h4, hba, h6, hr, hQ, hb0, hp9, hb27, hpb, hL1, hN1, hkb⟩ := segment_parameter_bounds h
  have hp1 : (1:ℝ) < p := by linarith
  have hp0 : (0:ℝ) < p := by linarith
  have ha0 : 0 < a := by linarith
  have hpa : (p:ℝ) < a := by
    have : (p:ℝ) * 1 ≤ (p:ℝ) * b' := mul_le_mul_of_nonneg_left (by linarith) hp0.le
    linarith
  have h1 : 1 < Real.logb p a := by
    rw [Real.lt_logb_iff_rpow_lt hp1 ha0, Real.rpow_one]; exact hpa
  have h8 : 0 < 8 * a + r := by linarith
  have h1' : 1 < Real.logb p (8 * a + r) := by
    rw [Real.lt_logb_iff_rpow_lt hp1 h8, Real.rpow_one]; linarith
  have h9 : 8 * a + r ≤ (p:ℝ) * a := by
    have : 9 * a ≤ (p:ℝ) * a := mul_le_mul_of_nonneg_right hp9 ha0.le
    linarith
  have h2' : Real.logb p (8 * a + r) ≤ 1 + Real.logb p a := by
    calc Real.logb p (8 * a + r) ≤ Real.logb p ((p:ℝ) * a) := Real.logb_le_logb_of_le hp1 h8 h9
      _ = 1 + Real.logb p a := by
        rw [Real.logb_mul hp0.ne' ha0.ne', Real.logb_self_eq_one hp1]
  have hlp : 1 ≤ Real.log p := by
    rw [Real.le_log_iff_exp_le hp0]
    have := Real.exp_one_lt_d9
    linarith
  have h5 : Real.logb p a ≤ Real.log a := by
    rw [← Real.log_div_log]
    exact div_le_self (by linarith) hlp
  unfold lgSeg
  refine ⟨h1, by linarith, by linarith, by linarith, h5, by linarith⟩
end Formalism.CountingSumsFrames
