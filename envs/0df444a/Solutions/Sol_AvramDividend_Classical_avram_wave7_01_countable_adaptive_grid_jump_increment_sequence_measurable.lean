-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_countable_adaptive_grid_jump_increment_sequence_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:06:54.42704+00:00
-- url     : https://prove2.me/submissions/6e5d9f35-4403-425a-8bbf-afe928bd45c1

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_measurable_countably_selected_raw_path_evaluation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- A countable family of path-adaptive sampled increments is product-measurable. -/
theorem solution
    (grid : ℕ → ℝ≥0)
    (left right : ℕ → (ℝ≥0 → ℝ) → ℕ)
    (hLeft : ∀ n, Measurable (left n))
    (hRight : ∀ n, Measurable (right n)) :
    Measurable (fun Y : ℝ≥0 → ℝ => fun n : ℕ =>
      Y (grid (right n Y)) - Y (grid (left n Y))) := by
  apply measurable_pi_lambda
  intro n
  exact
    (avram_wave7_01_measurable_countably_selected_raw_path_evaluation
      grid (right n) (hRight n)).sub
    (avram_wave7_01_measurable_countably_selected_raw_path_evaluation
      grid (left n) (hLeft n))
