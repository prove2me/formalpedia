-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_finite_grid_sum_eq_selected_injective_cells
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:45:57.656349+00:00
-- url     : https://prove2.me/submissions/57a505ac-e7de-43eb-affe-fbe04112f6ec

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal

/-- A finite grid sum supported on distinct selected jump cells equals
the corresponding sum indexed by the underlying genuine jump times. -/
theorem solution
    {α : Type*} [DecidableEq α]
    (S : Finset α) (n : ℕ) (j : α → ℕ)
    (hj : ∀ u ∈ S, j u < n + 1)
    (hinj : Set.InjOn j (↑S))
    (F : ℕ → ℝ)
    (hzero : ∀ i ∈ Finset.range (n + 1),
      i ∉ S.image j → F i = 0) :
    (∑ i ∈ Finset.range (n + 1), F i) =
      ∑ u ∈ S, F (j u) := by
  have hs : S.image j ⊆ Finset.range (n + 1) := by
    intro i hi
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (hj u hu)
  calc
    (∑ i ∈ Finset.range (n + 1), F i) =
        ∑ i ∈ S.image j, F i :=
      (Finset.sum_subset hs hzero).symm
    _ = ∑ u ∈ S, F (j u) := Finset.sum_image hinj
