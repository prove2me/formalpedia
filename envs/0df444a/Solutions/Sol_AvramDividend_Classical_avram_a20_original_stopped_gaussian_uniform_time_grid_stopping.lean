-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_stopped_gaussian_uniform_time_grid_stopping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:51:01.200493+00:00
-- url     : https://prove2.me/submissions/cca1bd27-672b-44da-96aa-03c6ca8b48a8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
open MeasureTheory
open scoped NNReal ENNReal

/-- Every physical Gaussian time-grid cell clipped to the original stopped ruin clock is a bounded stopping time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (n m i : ℕ) :
    let c : ℝ≥0 := (i : ℝ≥0) *
      ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0))
    let τ : Ω → ℝ≥0 := fun ω => min c (σ ω)
    IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) ∧
    (∀ ω, τ ω ≤ c) ∧
    (∀ ω, τ ω ≤ σ ω)  := by
  dsimp
  constructor
  · apply AvramDividend.Classical.isStoppingTime_withTop_of_le_events
    intro t
    by_cases hct :
        (i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)) ≤ t
    all_goals simp only [Nat.cast_add, Nat.cast_one] at hct
    · have hUniv :
          {ω : Ω | min
            ((i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)))
            (σ ω) ≤ t} = Set.univ := by
        ext ω
        simp [min_le_iff, hct]
      rw [hUniv]
      exact MeasurableSet.univ
    · have hEq :
          {ω : Ω | min
            ((i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)))
            (σ ω) ≤ t} = {ω : Ω | σ ω ≤ t} := by
        ext ω
        simp [min_le_iff, hct]
      rw [hEq]
      simpa only [WithTop.coe_le_coe] using
        (hσstop.measurableSet_le t)
  constructor
  · intro ω
    exact min_le_left _ _
  · intro ω
    exact min_le_right _ _
