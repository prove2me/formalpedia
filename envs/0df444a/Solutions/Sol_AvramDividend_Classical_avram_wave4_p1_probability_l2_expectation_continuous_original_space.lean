-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_probability_l2_expectation_continuous_original_space
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T23:59:24.803745+00:00
-- url     : https://prove2.me/submissions/db4fb93b-2eda-47d3-8937-0be40e997e7f

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal InnerProductSpace

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] :
    Continuous (fun F : Lp ℝ (2 : ℝ≥0∞) P => ∫ ω, F ω ∂P) := by
  have hfinite : P Set.univ ≠ ∞ := (measure_lt_top P Set.univ).ne
  let c : Lp ℝ (2 : ℝ≥0∞) P :=
    indicatorConstLp (2 : ℝ≥0∞) MeasurableSet.univ hfinite (1 : ℝ)
  have hEq (F : Lp ℝ (2 : ℝ≥0∞) P) :
      (∫ ω, F ω ∂P) = ⟪c, F⟫_ℝ := by
    have h := MeasureTheory.L2.inner_indicatorConstLp_one
      (s := Set.univ) (μ := P) MeasurableSet.univ hfinite F
    simpa [c] using h.symm
  have hc : Continuous (fun F : Lp ℝ (2 : ℝ≥0∞) P => ⟪c, F⟫_ℝ) :=
    continuous_const.inner continuous_id
  simpa only [hEq] using hc
