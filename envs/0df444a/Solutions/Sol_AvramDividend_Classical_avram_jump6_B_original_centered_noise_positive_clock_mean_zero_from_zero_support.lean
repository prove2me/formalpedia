-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_centered_noise_positive_clock_mean_zero_from_zero_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:31:28.86183+00:00
-- url     : https://prove2.me/submissions/4d6a7e7f-0f53-4c9a-936e-3d5179d9054b

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (σ : Ω → ℝ≥0) (hσmeas : Measurable σ)
    (M : Ω → ℝ) (hMI : Integrable M P)
    (hMzero : ∀ ω, σ ω = 0 → M ω = 0)
    (hMmean : (∫ ω, M ω ∂P) = 0) :
    (∫ ω in {ω | 0 < σ ω}, M ω ∂P) = 0 := by
  let A : Set Ω := {ω | 0 < σ ω}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hσmeas
  have hPoint : (A.indicator M) = M := by
    funext ω
    by_cases h : ω ∈ A
    · simp [Set.indicator_of_mem h]
    · have hz : σ ω = 0 := by
        have hn : ¬ 0 < σ ω := h
        exact le_antisymm (le_of_not_gt hn) zero_le
      simp [Set.indicator_of_notMem h, hMzero ω hz]
  rw [← MeasureTheory.integral_indicator hA]
  rw [hPoint]
  exact hMmean