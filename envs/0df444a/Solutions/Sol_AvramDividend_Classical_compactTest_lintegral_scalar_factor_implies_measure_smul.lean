-- Prove2me | solution 1 for AvramDividend.Classical.compactTest_lintegral_scalar_factor_implies_measure_smul
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:22:05.31098+00:00
-- url     : https://prove2.me/submissions/929f1a1d-faeb-4160-9965-50dee6c81628

import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_measure_eq_of_compactTest_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

/-- Scalar factorisation on compact nonnegative test integrals determines the scaled law. -/
theorem solution
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [LocallyCompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {μ ν : Measure Y} (c : ℝ≥0∞)
    [μ.Regular] [(c • ν).Regular]
    [IsFiniteMeasureOnCompacts μ]
    [IsFiniteMeasureOnCompacts (c • ν)]
    (h : ∀ f : CompactlySupportedContinuousMap Y ℝ≥0,
      (∫⁻ y, ((f y : ℝ≥0) : ℝ≥0∞) ∂μ) =
      c * (∫⁻ y, ((f y : ℝ≥0) : ℝ≥0∞) ∂ν)) :
    μ = c • ν := by
  apply AvramDividend.Classical.measure_eq_of_compactTest_lintegral
  intro f
  simpa only [lintegral_smul_measure, smul_eq_mul] using (h f)
