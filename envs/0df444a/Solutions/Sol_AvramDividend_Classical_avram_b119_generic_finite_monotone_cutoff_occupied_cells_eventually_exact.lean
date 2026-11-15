-- Prove2me | solution 1 for AvramDividend.Classical.avram_b119_generic_finite_monotone_cutoff_occupied_cells_eventually_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:25:54.702185+00:00
-- url     : https://prove2.me/submissions/c8d36e72-5aa0-4c8d-94bd-03889e243b98

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b117_generic_finite_marked_cells_one_cutoff_captures_all
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
noncomputable section

/-- A monotone finite family of marked cutoff grids that jointly exhausts all genuinely marked cells becomes exact at one cutoff. -/
theorem solution
    {ι : Type*} (S : Finset ι)
    (J : ℕ → Finset ι)
    (hSub : ∀ n, J n ⊆ S)
    (hMono : ∀ n m, n ≤ m → J n ⊆ J m)
    (hCover : ∀ i ∈ S, ∃ n : ℕ, i ∈ J n) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → J n = S := by
  classical
  obtain ⟨N, hN⟩ :=
    avram_b117_generic_finite_marked_cells_one_cutoff_captures_all
      S (fun k i => i ∈ J k)
      (by
        intro i a b hab hi
        exact hMono a b hab hi)
      hCover
  refine ⟨N, ?_⟩
  intro n hn
  apply Finset.Subset.antisymm (hSub n)
  intro i hi
  exact hMono N n hn (hN i hi)
