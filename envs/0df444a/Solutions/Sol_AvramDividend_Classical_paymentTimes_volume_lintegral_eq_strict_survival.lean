-- Prove2me | solution 1 for AvramDividend.Classical.paymentTimes_volume_lintegral_eq_strict_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:10:43.706603+00:00
-- url     : https://prove2.me/submissions/9a730d63-9c98-42de-9fcd-d50c39046e21

import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Stopping an ordinary time integral at the original payment set agrees with
the strict positive-time survival kernel; time zero is Lebesgue-null. -/
theorem solution (σ : ℝ≥0∞) (w : ℝ → ℝ≥0∞) :
    (∫⁻ t in paymentTimes σ, w t ∂volume) =
    (∫⁻ t in Ioi (0 : ℝ),
      (if ENNReal.ofReal t < σ then w t else 0) ∂volume) := by
  rw [← lintegral_indicator (paymentTimes_measurable σ) w]
  rw [← lintegral_indicator measurableSet_Ioi
    (fun t : ℝ => if ENNReal.ofReal t < σ then w t else 0)]
  apply lintegral_congr_ae
  have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
    rw [ae_iff]
    simpa using (show volume ({0} : Set ℝ) = 0 by simp)
  filter_upwards [hne] with t ht
  by_cases hpos : 0 < t
  · have hge : 0 ≤ t := le_of_lt hpos
    simp [Set.indicator, paymentTimes, hpos, hge, ht]
  · have hlt : t < 0 := lt_of_le_of_ne (le_of_not_gt hpos) ht
    have hnotge : ¬ (0 ≤ t) := not_le.mpr hlt
    simp [Set.indicator, paymentTimes, hpos, hnotge, hlt]
