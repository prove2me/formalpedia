-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_dense_grid_all_candidate_exact_marked_Borel_series
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:13:59.869487+00:00
-- url     : https://prove2.me/submissions/fcd8cc75-e22c-4a31-9c06-44045e8d988d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_path_countable_measurable_marked_jump_count
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_measurable_right_grid_selector_for_jump_marks
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_measurable_left_grid_selector_for_jump_marks
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_dense_source_grid_has_strict_right_mark_sample
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_dense_source_grid_has_strict_left_mark_sample
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_source_grid_left_window_limit_for_random_time
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable


/-- Any countable measurable candidate time family admits measurable exact marks
and a Borel marked finite-horizon deduplicated sum via a fixed dense clock. -/
theorem solution
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (time : ℕ → (ℝ≥0 → ℝ) → ℝ≥0)
    (htime : ∀ k, Measurable (time k))
    (ε : ℕ → ℝ≥0) (hεpos : ∀ n, 0 < ε n)
    (hε : Tendsto ε atTop (𝓝 0))
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    ∃ mark : ℕ → (ℝ≥0 → ℝ) → ℝ,
      (∀ k, Measurable (mark k)) ∧
      (∀ (k : ℕ) (Y : ℝ≥0 → ℝ), 0 < time k Y →
        ContinuousWithinAt Y (Ici (time k Y)) (time k Y) →
        Tendsto Y (𝓝[<] (time k Y))
          (𝓝 (Function.leftLim Y (time k Y))) →
        mark k Y = Y (time k Y) - Function.leftLim Y (time k Y)) ∧
      Measurable (fun Y : ℝ≥0 → ℝ =>
        ∑' k : ℕ,
          if 0 < time k Y ∧ time k Y ≤ T ∧ mark k Y ∈ B ∧
              (∀ j : ℕ, j < k → time j Y ≠ time k Y)
          then (1 : ℝ≥0∞) else 0) := by
  classical
  have hRightEach (k n : ℕ) :
      ∃ r : (ℝ≥0 → ℝ) → ℕ,
        Measurable r ∧
        ∀ Y : ℝ≥0 → ℝ,
          time k Y < grid (r Y) ∧
          grid (r Y) < time k Y + ε n := by
    apply avram_wave7_01_measurable_right_grid_selector_for_jump_marks
      grid (time k) (htime k) (ε n)
    intro Y
    exact avram_wave7_01_dense_source_grid_has_strict_right_mark_sample
      grid hdense (time k Y) (ε n) (hεpos n)
  choose rightIndex hRightMeas hRightStrict using hRightEach
  have hLeftEach (k n : ℕ) :
      ∃ l : (ℝ≥0 → ℝ) → ℕ,
        Measurable l ∧
        ∀ Y : ℝ≥0 → ℝ, 0 < time k Y →
          grid (l Y) < time k Y ∧
          time k Y < grid (l Y) + ε n := by
    apply avram_wave7_01_measurable_left_grid_selector_for_jump_marks
      grid (time k) (htime k) (ε n)
    intro Y hPos
    exact avram_wave7_01_dense_source_grid_has_strict_left_mark_sample
      grid hdense (time k Y) (ε n) hPos (hεpos n)
  choose leftIndex hLeftMeas hLeftStrict using hLeftEach
  let lower : ℕ → ℕ → (ℝ≥0 → ℝ) → ℝ≥0 :=
    fun k n Y => time k Y - ε n
  have hRB (k : ℕ) (Y : ℝ≥0 → ℝ) (n : ℕ) :
      time k Y ≤ grid (rightIndex k n Y) ∧
        grid (rightIndex k n Y) ≤ time k Y + ε n :=
    ⟨(hRightStrict k n Y).1.le, (hRightStrict k n Y).2.le⟩
  have hLB (k : ℕ) (Y : ℝ≥0 → ℝ)
      (hPos : 0 < time k Y) (n : ℕ) :
      lower k n Y ≤ grid (leftIndex k n Y) ∧
        grid (leftIndex k n Y) < time k Y := by
    have hW := hLeftStrict k n Y hPos
    exact ⟨tsub_le_iff_right.mpr hW.2.le, hW.1⟩
  have hLL (k : ℕ) (Y : ℝ≥0 → ℝ) (hPos : 0 < time k Y) :
      Tendsto (fun n => lower k n Y) atTop (𝓝 (time k Y)) := by
    simpa only [lower] using
      avram_wave7_01_source_grid_left_window_limit_for_random_time
        (time k Y) ε hε
  exact avram_wave7_01_original_path_countable_measurable_marked_jump_count
    grid time htime rightIndex leftIndex hRightMeas hLeftMeas
    ε hε hRB lower hLB hLL T B hB
