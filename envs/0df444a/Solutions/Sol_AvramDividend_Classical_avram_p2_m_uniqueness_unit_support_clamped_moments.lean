-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_unit_support_clamped_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:29:00.068681+00:00
-- url     : https://prove2.me/submissions/9d1ae12c-4d76-4b44-98e8-cab77cdc5dd6

import Mathlib.MeasureTheory.Measure.FiniteMeasure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set BoundedContinuousFunction
open scoped NNReal ENNReal

/-- A bounded NNReal-valued test that agrees with `ofReal` on the unit
interval has the exact original monomial moment under any unit-supported
finite measure. -/
theorem solution (μ : FiniteMeasure ℝ) (f : ℝ →ᵇ ℝ≥0) (k : ℕ)
    (hunit : μ (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (hagree : ∀ z : ℝ, z ∈ Set.Icc (0 : ℝ) 1 →
      (f z : ℝ≥0∞) = ENNReal.ofReal z) :
    (∫⁻ z, (f z : ℝ≥0∞) ^ k ∂μ) =
      (∫⁻ z, (ENNReal.ofReal z) ^ k ∂μ) := by
  have hzero : (μ : Measure ℝ) (Set.Icc (0 : ℝ) 1)ᶜ = 0 :=
    (FiniteMeasure.null_iff_toMeasure_null μ _).mp hunit
  have hae : ∀ᵐ z ∂(μ : Measure ℝ), z ∈ Set.Icc (0 : ℝ) 1 :=
    (mem_ae_iff).2 hzero
  apply lintegral_congr_ae
  filter_upwards [hae] with z hz
  rw [hagree z hz]
