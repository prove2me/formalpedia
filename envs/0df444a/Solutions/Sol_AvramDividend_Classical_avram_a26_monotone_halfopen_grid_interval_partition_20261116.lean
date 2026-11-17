-- Prove2me | solution 1 for AvramDividend.Classical.avram_a26_monotone_halfopen_grid_interval_partition_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:28:04.836591+00:00
-- url     : https://prove2.me/submissions/06a79b39-f699-441d-bde2-2886283da6f3

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal
noncomputable section
theorem solution
    (u : ℕ → ℝ≥0) (hmono : Monotone u) (n : ℕ) :
    (⋃ i ∈ Finset.range n, Set.Ioc (u i) (u (i + 1))) =
      Set.Ioc (u 0) (u n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (⋃ i ∈ Finset.range (n + 1), Set.Ioc (u i) (u (i + 1))) =
          Set.Ioc (u n) (u (n + 1)) ∪ Set.Ioc (u 0) (u n) := by
            rw [Finset.range_add_one, Finset.set_biUnion_insert, ih]
        _ = Set.Ioc (u 0) (u (n + 1)) := by
          rw [union_comm]
          exact Set.Ioc_union_Ioc_eq_Ioc
            (hmono (Nat.zero_le n)) (hmono (Nat.le_succ n))
