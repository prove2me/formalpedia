-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_turn13_cofinal_mask_eventually_covers_finite_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:43:18.091636+00:00
-- url     : https://prove2.me/submissions/567e9bfc-06bb-452d-aab3-c953469a69a8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem solution
    (C : ℝ≥0∞) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k))
    (s : Finset ℕ) (z : ℕ → ℝ)
    (hz : ∀ i ∈ s, 0 < z i ∧ ENNReal.ofReal (z i) < C) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ i ∈ s, z i ∈ Icc (a k) (b k) := by
  classical
  revert hz
  induction s using Finset.induction_on with
  | empty =>
      intro hz
      refine ⟨0, ?_⟩
      intro k hk i hi
      simp at hi
  | @insert i s his ih =>
      intro hz
      have hi : 0 < z i ∧ ENNReal.ofReal (z i) < C :=
        hz i (Finset.mem_insert_self i s)
      obtain ⟨N, hN⟩ := hExh (z i) hi.1 hi.2
      have hzs : ∀ j ∈ s, 0 < z j ∧ ENNReal.ofReal (z j) < C := by
        intro j hj
        exact hz j (Finset.mem_insert_of_mem hj)
      obtain ⟨M, hM⟩ := ih hzs
      refine ⟨max N M, ?_⟩
      intro k hk j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hN k (le_trans (le_max_left N M) hk)
      · exact hM k (le_trans (le_max_right N M) hk) j hj
