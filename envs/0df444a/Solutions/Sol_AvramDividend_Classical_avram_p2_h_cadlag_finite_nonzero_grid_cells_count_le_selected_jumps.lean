-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_finite_nonzero_grid_cells_count_le_selected_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:06:01.92358+00:00
-- url     : https://prove2.me/submissions/2024dcd4-fe68-4442-bfba-f932bbe4999e

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped BigOperators

/-- Every nonzero grid test cell belongs to the image of a finite
selected actual-jump set; cardinality cannot exceed the jump count. -/
theorem solution
    {α : Type*} (S : Finset α) (j : α → ℕ)
    (n : ℕ) (g : ℕ → ℝ)
    (hzero : ∀ i ∈ Finset.range (n + 1),
      i ∉ S.image j → g i = 0) :
    ((Finset.range (n + 1)).filter (fun i => g i ≠ 0)).card ≤ S.card := by
  classical
  calc
    ((Finset.range (n + 1)).filter (fun i => g i ≠ 0)).card ≤
      (S.image j).card := by
        apply Finset.card_le_card
        intro i hi
        obtain ⟨hiRange, hiNonzero⟩ := Finset.mem_filter.mp hi
        by_contra hnot
        exact hiNonzero (hzero i hiRange hnot)
    _ ≤ S.card := Finset.card_image_le
