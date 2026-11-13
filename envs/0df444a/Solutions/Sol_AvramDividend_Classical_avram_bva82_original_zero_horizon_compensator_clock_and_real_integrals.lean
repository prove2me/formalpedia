-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva82_original_zero_horizon_compensator_clock_and_real_integrals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:25:57.687241+00:00
-- url     : https://prove2.me/submissions/15e57677-f2cb-47f7-a501-079d9e2d8788

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution :
    let μ : Measure ℝ≥0 :=
      (((volume : Measure ℝ).restrict (Icc (0 : ℝ) 0)).map Real.toNNReal)
    μ = 0 ∧ ∀ f : ℝ≥0 → ℝ, (∫ t, f t ∂μ) = 0 := by
  intro μ
  have hv : (volume : Measure ℝ) (Icc (0 : ℝ) 0) = 0 := by simp
  have hr : (volume : Measure ℝ).restrict (Icc (0 : ℝ) 0) = 0 :=
    Measure.restrict_zero_set hv
  have hμ : μ = 0 := by
    dsimp [μ]
    rw [hr]
    exact Measure.map_zero Real.toNNReal
  refine ⟨hμ, ?_⟩
  intro f
  rw [hμ]
  simp
