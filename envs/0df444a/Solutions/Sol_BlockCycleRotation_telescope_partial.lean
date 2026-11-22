-- Prove2me | solution 1 for BlockCycleRotation.telescope_partial
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-05T11:02:59.522312+00:00
-- url     : https://prove2.me/submissions/b85ac75d-7fb7-4c4d-9aea-dc238252eaa4

import Mathlib

open Real Finset Filter Topology

theorem solution (n N : ℕ) (h : n ≤ N) :
    ∑ j ∈ Finset.range N, (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + (n : ℝ) + 1))
      = (∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1))
        - ∑ j ∈ Finset.Ico N (N + n), 1 / ((j : ℝ) + 1) := by
  have h1 : ∑ j ∈ Finset.range N, 1 / ((j : ℝ) + (n : ℝ) + 1)
      = ∑ j ∈ Finset.Ico n (N + n), 1 / ((j : ℝ) + 1) := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring_nf
  rw [Finset.sum_sub_distrib, h1, Finset.range_eq_Ico, Finset.range_eq_Ico]
  have s1 : (∑ j ∈ Finset.Ico 0 n, 1 / ((j : ℝ) + 1))
      + ∑ j ∈ Finset.Ico n N, 1 / ((j : ℝ) + 1)
      = ∑ j ∈ Finset.Ico 0 N, 1 / ((j : ℝ) + 1) :=
    Finset.sum_Ico_consecutive _ (Nat.zero_le n) h
  have s2 : (∑ j ∈ Finset.Ico n N, 1 / ((j : ℝ) + 1))
      + ∑ j ∈ Finset.Ico N (N + n), 1 / ((j : ℝ) + 1)
      = ∑ j ∈ Finset.Ico n (N + n), 1 / ((j : ℝ) + 1) :=
    Finset.sum_Ico_consecutive _ h (by omega)
  linarith
