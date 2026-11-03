-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_measurable_shrinking_right_grid_samples_recover_original_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:11:02.135638+00:00
-- url     : https://prove2.me/submissions/a9b01c93-0b6d-4154-b866-d63338d89764

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_measurable_right_grid_selector_for_jump_marks
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_measurable_countably_selected_raw_path_evaluation
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_right_continuous_selected_grid_path_values_converge
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original-path right limits have measurable approximations at every precision. -/
theorem solution
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (t : (ℝ≥0 → ℝ) → ℝ≥0) (ht : Measurable t)
    (ε : ℕ → ℝ≥0) (hεpos : ∀ n, 0 < ε n)
    (hε : Tendsto ε atTop (𝓝 0)) :
    ∃ index : ℕ → (ℝ≥0 → ℝ) → ℕ,
      (∀ n : ℕ, Measurable (index n)) ∧
      (∀ n : ℕ, Measurable (fun Y : ℝ≥0 → ℝ =>
        Y (grid (index n Y)))) ∧
      (∀ (n : ℕ) (Y : ℝ≥0 → ℝ),
        t Y < grid (index n Y) ∧ grid (index n Y) < t Y + ε n) ∧
      ∀ Y : ℝ≥0 → ℝ,
        ContinuousWithinAt Y (Ici (t Y)) (t Y) →
        Tendsto (fun n : ℕ => Y (grid (index n Y)))
          atTop (𝓝 (Y (t Y))) := by
  have hExist (n : ℕ) (Y : ℝ≥0 → ℝ) :
      ∃ m : ℕ, t Y < grid m ∧ grid m < t Y + ε n := by
    have hInt : t Y < t Y + ε n := lt_add_of_pos_right _ (hεpos n)
    obtain ⟨v, ⟨m, rfl⟩, hv⟩ := hdense.exists_between hInt
    exact ⟨m, hv⟩
  have hSelector (n : ℕ) :
      ∃ q : (ℝ≥0 → ℝ) → ℕ, Measurable q ∧
        ∀ Y, t Y < grid (q Y) ∧ grid (q Y) < t Y + ε n :=
    avram_wave7_01_measurable_right_grid_selector_for_jump_marks
      grid t ht (ε n) (hExist n)
  choose index hIndex hBounds using hSelector
  refine ⟨index, hIndex, ?_, hBounds, ?_⟩
  · intro n
    exact avram_wave7_01_measurable_countably_selected_raw_path_evaluation
      grid (index n) (hIndex n)
  · intro Y hRight
    apply avram_wave7_01_right_continuous_selected_grid_path_values_converge
      grid t ε hε index
      (fun Z n => ⟨le_of_lt (hBounds n Z).1, le_of_lt (hBounds n Z).2⟩)
      Y hRight
