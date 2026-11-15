-- Prove2me | solution 2 for AvramDividend.Classical.avram_b119_generic_finite_monotone_cutoff_occupied_cells_eventually_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:26:19.135743+00:00
-- url     : https://prove2.me/submissions/61538345-7e2b-4cdb-ba78-6885c379e3ce

import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical Set Filter
noncomputable section

theorem solution
    {ι : Type*} (S : Finset ι)
    (J : ℕ → Finset ι)
    (hSub : ∀ n, J n ⊆ S)
    (hMono : ∀ n m, n ≤ m → J n ⊆ J m)
    (hCover : ∀ i ∈ S, ∃ n : ℕ, i ∈ J n) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → J n = S := by
  classical
  have hAll : ∀ᶠ n in (atTop : Filter ℕ), ∀ i ∈ S, i ∈ J n := by
    rw [Finset.eventually_all]
    intro i hi
    obtain ⟨m, him⟩ := hCover i hi
    exact (Filter.eventually_atTop.2 ⟨m, fun n hmn => hMono m n hmn him⟩)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hAll
  refine ⟨N, fun n hn => Finset.Subset.antisymm (hSub n) ?_⟩
  intro i hi
  exact hN n hn i hi
