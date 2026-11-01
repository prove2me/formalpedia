-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_probability_l2_expectation_contracts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:05:13.152959+00:00
-- url     : https://prove2.me/submissions/ea38a22b-3c86-4546-8bc6-8f7003c60185

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal InnerProductSpace

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Lp ℝ (2 : ℝ≥0∞) P) :
    |∫ ω, F ω ∂P| ≤ ‖F‖ := by
  have hfinite : P Set.univ ≠ ∞ := (measure_lt_top P Set.univ).ne
  let c : Lp ℝ (2 : ℝ≥0∞) P :=
    indicatorConstLp (2 : ℝ≥0∞) MeasurableSet.univ hfinite (1 : ℝ)
  have hnorm : ‖c‖ = 1 := by
    change ‖indicatorConstLp (2 : ℝ≥0∞)
      MeasurableSet.univ hfinite (1 : ℝ)‖ = 1
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp [measureReal_def]
  have hinner : ⟪c, F⟫_ℝ = ∫ ω, F ω ∂P := by
    have h := MeasureTheory.L2.inner_indicatorConstLp_one
      (s := Set.univ) (μ := P) MeasurableSet.univ hfinite F
    simpa [c] using h
  calc
    |∫ ω, F ω ∂P| = ‖⟪c, F⟫_ℝ‖ := by
      simp [hinner, Real.norm_eq_abs]
    _ ≤ ‖c‖ * ‖F‖ := norm_inner_le_norm c F
    _ = ‖F‖ := by simp [hnorm]
