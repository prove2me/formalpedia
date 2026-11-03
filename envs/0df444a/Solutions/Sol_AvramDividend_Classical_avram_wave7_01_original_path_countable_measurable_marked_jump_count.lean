-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_original_path_countable_measurable_marked_jump_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:55:16.345281+00:00
-- url     : https://prove2.me/submissions/84b3b25f-e18f-41a4-a165-3d718f98b528

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_exact_measurable_jump_mark_from_two_grid_families
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_deduplicated_countable_borel_jump_candidates_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- All positive enumerated jump marks admit measurable deduplicated counting. -/
theorem solution
    (grid : ℕ → ℝ≥0)
    (time : ℕ → (ℝ≥0 → ℝ) → ℝ≥0)
    (htime : ∀ k, Measurable (time k))
    (rightIndex leftIndex : ℕ → ℕ → (ℝ≥0 → ℝ) → ℕ)
    (hRightIndex : ∀ k n, Measurable (rightIndex k n))
    (hLeftIndex : ∀ k n, Measurable (leftIndex k n))
    (ε : ℕ → ℝ≥0) (hε : Tendsto ε atTop (𝓝 0))
    (hRightBounds : ∀ (k : ℕ) (Y : ℝ≥0 → ℝ) (n : ℕ),
      time k Y ≤ grid (rightIndex k n Y) ∧
      grid (rightIndex k n Y) ≤ time k Y + ε n)
    (lower : ℕ → ℕ → (ℝ≥0 → ℝ) → ℝ≥0)
    (hLeftBounds : ∀ (k : ℕ) (Y : ℝ≥0 → ℝ), 0 < time k Y →
      ∀ n, lower k n Y ≤ grid (leftIndex k n Y) ∧
        grid (leftIndex k n Y) < time k Y)
    (hLower : ∀ (k : ℕ) (Y : ℝ≥0 → ℝ), 0 < time k Y →
      Tendsto (fun n => lower k n Y) atTop (𝓝 (time k Y)))
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
  have hEach (k : ℕ) :
      ∃ m : (ℝ≥0 → ℝ) → ℝ,
        Measurable m ∧
        ∀ Y : ℝ≥0 → ℝ, 0 < time k Y →
          ContinuousWithinAt Y (Ici (time k Y)) (time k Y) →
          Tendsto Y (𝓝[<] (time k Y))
            (𝓝 (Function.leftLim Y (time k Y))) →
          m Y = Y (time k Y) - Function.leftLim Y (time k Y) :=
    avram_wave7_01_exact_measurable_jump_mark_from_two_grid_families
      grid (time k) (rightIndex k) (leftIndex k)
      (hRightIndex k) (hLeftIndex k)
      ε hε (hRightBounds k) (lower k) (hLeftBounds k) (hLower k)
  choose mark hMark hExact using hEach
  refine ⟨mark, hMark, hExact, ?_⟩
  exact avram_wave7_01_deduplicated_countable_borel_jump_candidates_measurable
    time mark htime hMark T B hB
