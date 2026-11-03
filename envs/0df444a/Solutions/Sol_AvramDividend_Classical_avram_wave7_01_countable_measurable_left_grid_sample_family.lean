-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_countable_measurable_left_grid_sample_family
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:09:26.459474+00:00
-- url     : https://prove2.me/submissions/3913abd0-ab15-4649-aa19-b462ae892659

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_measurable_left_grid_selector_for_jump_marks
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_measurable_countably_selected_raw_path_evaluation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Measurable left-grid samples on the actual raw coordinate path space. -/
theorem solution
    (grid : ℕ → ℝ≥0)
    (t : (ℝ≥0 → ℝ) → ℝ≥0) (ht : Measurable t)
    (ε : ℕ → ℝ≥0)
    (hExist : ∀ (n : ℕ) (Y : ℝ≥0 → ℝ), 0 < t Y →
      ∃ m : ℕ, grid m < t Y ∧ t Y < grid m + ε n) :
    ∃ index : ℕ → (ℝ≥0 → ℝ) → ℕ,
      (∀ n : ℕ, Measurable (index n)) ∧
      (∀ n : ℕ, Measurable (fun Y : ℝ≥0 → ℝ =>
        Y (grid (index n Y)))) ∧
      ∀ (n : ℕ) (Y : ℝ≥0 → ℝ), 0 < t Y →
        grid (index n Y) < t Y ∧
        t Y < grid (index n Y) + ε n := by
  have hSelector (n : ℕ) :
      ∃ q : (ℝ≥0 → ℝ) → ℕ, Measurable q ∧
        ∀ Y, 0 < t Y →
          grid (q Y) < t Y ∧ t Y < grid (q Y) + ε n :=
    avram_wave7_01_measurable_left_grid_selector_for_jump_marks
      grid t ht (ε n) (hExist n)
  choose index hIndex hBounds using hSelector
  refine ⟨index, hIndex, ?_, hBounds⟩
  intro n
  exact avram_wave7_01_measurable_countably_selected_raw_path_evaluation
    grid (index n) (hIndex n)
