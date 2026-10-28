-- Prove2me | solution 1 for AvramDividend.Classical.paymentTimes_lintegral_smul_volume
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:17:03.155781+00:00
-- url     : https://prove2.me/submissions/3e29bee8-a1d6-42b1-b208-b3bbb10bb853

import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A constant drift-density factor can be transferred from Lebesgue measure
to the discounted integrand over the original prescribed payment times. -/
theorem solution
    (σ : ℝ≥0∞) (c : ℝ≥0∞) (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ t in paymentTimes σ, w t ∂(c • volume)) =
    (∫⁻ t in paymentTimes σ, c * w t ∂volume) := by
  have hs : MeasurableSet (paymentTimes σ) := paymentTimes_measurable σ
  calc
    (∫⁻ t in paymentTimes σ, w t ∂(c • volume)) =
        (∫⁻ t, (paymentTimes σ).indicator w t ∂(c • volume)) :=
      (lintegral_indicator hs w).symm
    _ = c • (∫⁻ t, (paymentTimes σ).indicator w t ∂volume) :=
      lintegral_smul_measure c _
    _ = c * (∫⁻ t, (paymentTimes σ).indicator w t ∂volume) := rfl
    _ = (∫⁻ t, c * (paymentTimes σ).indicator w t ∂volume) :=
      (lintegral_const_mul c (hw.indicator hs)).symm
    _ = (∫⁻ t in paymentTimes σ, c * w t ∂volume) := by
      rw [← lintegral_indicator hs (fun t : ℝ => c * w t)]
      apply lintegral_congr
      intro t
      by_cases ht : t ∈ paymentTimes σ
      · simp [Set.indicator, ht]
      · simp [Set.indicator, ht]
