-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_exact_measurable_jump_mark_from_two_grid_families
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:16:51.452887+00:00
-- url     : https://prove2.me/submissions/36d099cf-f768-4801-bc32-d3495beb45e4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_exact_jump_mark_measurable_extension_from_sample_limits
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_right_continuous_selected_grid_path_values_converge
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_measurable_countably_selected_raw_path_evaluation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Measurable exact jump marks from left and right evaluations of raw paths. -/
theorem solution
    (grid : ℕ → ℝ≥0)
    (t : (ℝ≥0 → ℝ) → ℝ≥0)
    (rightIndex leftIndex : ℕ → (ℝ≥0 → ℝ) → ℕ)
    (hRightIndex : ∀ n, Measurable (rightIndex n))
    (hLeftIndex : ∀ n, Measurable (leftIndex n))
    (ε : ℕ → ℝ≥0) (hε : Tendsto ε atTop (𝓝 0))
    (hRightBounds : ∀ (Y : ℝ≥0 → ℝ) (n : ℕ),
      t Y ≤ grid (rightIndex n Y) ∧
      grid (rightIndex n Y) ≤ t Y + ε n)
    (lower : ℕ → (ℝ≥0 → ℝ) → ℝ≥0)
    (hLeftBounds : ∀ Y : ℝ≥0 → ℝ, 0 < t Y →
      ∀ n, lower n Y ≤ grid (leftIndex n Y) ∧
        grid (leftIndex n Y) < t Y)
    (hLower : ∀ Y : ℝ≥0 → ℝ, 0 < t Y →
      Tendsto (fun n => lower n Y) atTop (𝓝 (t Y))) :
    ∃ mark : (ℝ≥0 → ℝ) → ℝ,
      Measurable mark ∧
      ∀ Y : ℝ≥0 → ℝ, 0 < t Y →
        ContinuousWithinAt Y (Ici (t Y)) (t Y) →
        Tendsto Y (𝓝[<] (t Y))
          (𝓝 (Function.leftLim Y (t Y))) →
        mark Y = Y (t Y) - Function.leftLim Y (t Y) := by
  have hRM (n : ℕ) : Measurable
      (fun Y : ℝ≥0 → ℝ => Y (grid (rightIndex n Y))) :=
    avram_wave7_01_measurable_countably_selected_raw_path_evaluation
      grid (rightIndex n) (hRightIndex n)
  have hLM (n : ℕ) : Measurable
      (fun Y : ℝ≥0 → ℝ => Y (grid (leftIndex n Y))) :=
    avram_wave7_01_measurable_countably_selected_raw_path_evaluation
      grid (leftIndex n) (hLeftIndex n)
  obtain ⟨mark, hMark, hExact⟩ :=
    avram_wave7_01_exact_jump_mark_measurable_extension_from_sample_limits
      t (fun n Y => Y (grid (rightIndex n Y)))
        (fun n Y => Y (grid (leftIndex n Y))) hRM hLM
  refine ⟨mark, hMark, ?_⟩
  intro Y hPos hRight hLeft
  apply hExact Y
  · exact avram_wave7_01_right_continuous_selected_grid_path_values_converge
      grid t ε hε rightIndex hRightBounds Y hRight
  · have hConst : Tendsto (fun _ : ℕ => t Y) atTop (𝓝 (t Y)) :=
      tendsto_const_nhds
    have hGrid : Tendsto (fun n : ℕ => grid (leftIndex n Y))
        atTop (𝓝 (t Y)) :=
      Filter.Tendsto.squeeze (hLower Y hPos) hConst
        (fun n => (hLeftBounds Y hPos n).1)
        (fun n => le_of_lt (hLeftBounds Y hPos n).2)
    have hWithin : Tendsto (fun n : ℕ => grid (leftIndex n Y))
        atTop (𝓝[<] (t Y)) := by
      apply (tendsto_nhdsWithin_iff).2
      exact ⟨hGrid, Filter.Eventually.of_forall
        (fun n => (hLeftBounds Y hPos n).2)⟩
    exact Filter.Tendsto.comp hLeft hWithin
