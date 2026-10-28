-- Prove2me | solution 1 for AvramDividend.Classical.measure_eq_of_compactTest_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:05:46.475526+00:00
-- url     : https://prove2.me/submissions/67ac945c-667c-431f-9e79-36d3fafbef66

import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

/-- Compactly supported nonnegative test-function lower integrals determine regular measures. -/
theorem solution
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [LocallyCompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {μ ν : Measure Y} [μ.Regular] [ν.Regular]
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (h : ∀ f : CompactlySupportedContinuousMap Y ℝ≥0,
      (∫⁻ y, ((f y : ℝ≥0) : ℝ≥0∞) ∂μ) =
      (∫⁻ y, ((f y : ℝ≥0) : ℝ≥0∞) ∂ν)) :
    μ = ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported_nnreal
  intro f
  have hμ :
      (∫⁻ y, ((f y : ℝ≥0) : ℝ≥0∞) ∂μ).toReal =
        ∫ y, (f y : ℝ) ∂μ := by
    simpa only [CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply] using
      (f.toBoundedContinuousFunction.toReal_lintegral_coe_eq_integral μ)
  have hν :
      (∫⁻ y, ((f y : ℝ≥0) : ℝ≥0∞) ∂ν).toReal =
        ∫ y, (f y : ℝ) ∂ν := by
    simpa only [CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply] using
      (f.toBoundedContinuousFunction.toReal_lintegral_coe_eq_integral ν)
  exact hμ.symm.trans ((congrArg ENNReal.toReal (h f)).trans hν)
