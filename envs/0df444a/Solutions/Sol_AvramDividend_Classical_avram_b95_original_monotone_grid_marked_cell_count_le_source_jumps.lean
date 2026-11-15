-- Prove2me | solution 1 for AvramDividend.Classical.avram_b95_original_monotone_grid_marked_cell_count_le_source_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:16:04.772399+00:00
-- url     : https://prove2.me/submissions/1cbc9d23-4496-43dd-ad33-6e1d8b0b6c9d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_monotone_marked_grid_index_unique
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Distinct genuinely marked monotone source grid cells require distinct original source jump times. -/
theorem solution
    (grid : ℕ → ℝ≥0) (hmono : Monotone grid)
    (J : Finset ℕ) (F : Finset ℝ≥0)
    (hJ : ∀ i ∈ J, ∃ u ∈ F,
      u ∈ Ioc (grid i) (grid (i + 1))) :
    J.card ≤ F.card := by
  classical
  let g : ℕ → ℝ≥0 := fun i =>
    if hi : i ∈ J then Classical.choose (hJ i hi) else 0
  have hG (i : ℕ) (hi : i ∈ J) :
      g i ∈ F ∧ g i ∈ Ioc (grid i) (grid (i + 1)) := by
    simpa only [g, dif_pos hi] using
      (Classical.choose_spec (hJ i hi))
  have hMap : Set.MapsTo g (J : Set ℕ) (F : Set ℝ≥0) := by
    intro i hi
    exact (hG i hi).1
  have hInj : Set.InjOn g (J : Set ℕ) := by
    intro i hi j hj heq
    have hLeft := (hG i hi).2
    have hRight : g i ∈ Ioc (grid j) (grid (j + 1)) := by
      simpa only [heq] using (hG j hj).2
    exact avram_wave7_06_monotone_marked_grid_index_unique
      grid hmono (g i) i j hLeft hRight
  exact Finset.card_le_card_of_injOn g hMap hInj
