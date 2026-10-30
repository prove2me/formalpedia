-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_paymentTimes_Ioi_integral_eq_positive_weight
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T16:01:04.449366+00:00
-- url     : https://prove2.me/submissions/36e6532b-d9dd-40a5-bfd8-9add0c8572f1

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal Classical

/-- Intersecting the true stopped payment set with positive real times is
equivalent to the same positive-time indicator on the stopped Stieltjes reward. -/
theorem solution
    (μ : Measure ℝ) (τ : ℝ≥0∞) (w : ℝ → ℝ≥0∞) :
    (∫⁻ r in Ioi (0 : ℝ) ∩ paymentTimes τ, w r ∂μ) =
    (∫⁻ r in paymentTimes τ, if 0 < r then w r else 0 ∂μ) := by
  have hRight :
      (∫⁻ r in paymentTimes τ, if 0 < r then w r else 0 ∂μ) =
      (∫⁻ r in Ioi (0 : ℝ), w r ∂(μ.restrict (paymentTimes τ))) := by
    rw [← lintegral_indicator measurableSet_Ioi w]
    apply lintegral_congr
    intro r
    by_cases hr : 0 < r <;> simp [Set.indicator, hr]
  rw [hRight]
  change (∫⁻ r, w r ∂μ.restrict (Ioi (0 : ℝ) ∩ paymentTimes τ)) =
    (∫⁻ r, w r ∂(μ.restrict (paymentTimes τ)).restrict (Ioi (0 : ℝ)))
  rw [Measure.restrict_restrict]
  exact measurableSet_Ioi
