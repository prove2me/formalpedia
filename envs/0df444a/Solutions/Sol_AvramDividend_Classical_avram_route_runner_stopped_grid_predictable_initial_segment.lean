-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_runner_stopped_grid_predictable_initial_segment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:42:20.811173+00:00
-- url     : https://prove2.me/submissions/9e23e21a-b1ca-40ae-8c45-32115ad3d445

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_monotone_stopped_clock_prefix_selector
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn23_original_stopped_physical_grid_selection_predictable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original right-continuous stopped-clock masks form predictable prefix events. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ) :
    ∃ k : Ω → ℕ,
      (∀ ω, k ω ≤ m) ∧
      (∀ ω i, i < m →
        ((u i : WithTop ℝ≥0) < τ ω ↔ i < k ω)) ∧
      (∀ i, MeasurableSet[𝓕.rightCont (u i)]
        {ω : Ω | i < k ω}) := by
  obtain ⟨k, hkBound, hMask⟩ :=
    avram_route_runner_monotone_stopped_clock_prefix_selector τ u hu m
  refine ⟨k, hkBound, hMask, ?_⟩
  intro i
  by_cases hi : i < m
  · have hEq : {ω : Ω | i < k ω} =
        {ω : Ω | (u i : WithTop ℝ≥0) < τ ω} := by
      ext ω
      exact (hMask ω i hi).symm
    rw [hEq]
    exact avram_bv_env3_turn23_original_stopped_physical_grid_selection_predictable
      X τ hStop u i
  · have hEq : {ω : Ω | i < k ω} = (∅ : Set Ω) := by
      ext ω
      have hNo : ¬ i < k ω := by
        have hBound := hkBound ω
        omega
      simp [hNo]
    rw [hEq]
    exact @MeasurableSet.empty Ω (𝓕.rightCont (u i))
