-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn12_original_stopping_grid_prefix_count_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:56:07.928402+00:00
-- url     : https://prove2.me/submissions/56d8d3d0-c808-44f0-9610-a58fea86f47f

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn12_monotone_stopped_grid_filter_card_prefix_iff
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn23_original_stopped_physical_grid_selection_predictable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Counting the true prior physical mesh cells yields an adapted stopping-index
selection at the left endpoint of every cell of the original Lévy process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ) :
    ∀ i, MeasurableSet[𝓕.rightCont (u i)]
      {ω : Ω | i < ((Finset.range m).filter
        (fun j => (u j : WithTop ℝ≥0) < τ ω)).card} := by
  classical
  intro i
  by_cases hi : i < m
  · have hEq : {ω : Ω | i < ((Finset.range m).filter
        (fun j => (u j : WithTop ℝ≥0) < τ ω)).card} =
        {ω : Ω | (u i : WithTop ℝ≥0) < τ ω} := by
      ext ω
      change (i < ((Finset.range m).filter
        (fun j => (u j : WithTop ℝ≥0) < τ ω)).card) ↔
        (u i : WithTop ℝ≥0) < τ ω
      rw [avram_bv_env3_turn12_monotone_stopped_grid_filter_card_prefix_iff u hu m i (τ ω)]
      simp [hi]
    rw [hEq]
    exact avram_bv_env3_turn23_original_stopped_physical_grid_selection_predictable
      X τ hStop u i
  · have hEq : {ω : Ω | i < ((Finset.range m).filter
        (fun j => (u j : WithTop ℝ≥0) < τ ω)).card} = ∅ := by
      ext ω
      change (i < ((Finset.range m).filter
        (fun j => (u j : WithTop ℝ≥0) < τ ω)).card) ↔ False
      rw [avram_bv_env3_turn12_monotone_stopped_grid_filter_card_prefix_iff u hu m i (τ ω)]
      simp [hi]
    rw [hEq]
    exact @MeasurableSet.empty Ω (𝓕.rightCont (u i))
