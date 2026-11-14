-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB257_monotone_grid_large_dividend_cell_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T15:54:50.143488+00:00
-- url     : https://prove2.me/submissions/75069a33-1950-4074-894a-42c182181e75

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset
noncomputable section

theorem solution
    (d : ℕ → ℝ) (hd : Monotone d) (epsilon : ℝ) (hEps : 0 < epsilon)
    (n : ℕ) :
    (((Finset.range n).filter (fun i => epsilon < d (i + 1) - d i)).card : ℝ) *
      epsilon ≤ d n - d 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hn : epsilon < d (n + 1) - d n
    · have hcard :
          ((Finset.range (n + 1)).filter (fun i => epsilon < d (i + 1) - d i)).card =
            ((Finset.range n).filter (fun i => epsilon < d (i + 1) - d i)).card + 1 := by
          simp [Finset.range_add_one, Finset.filter_insert, hn, Finset.mem_range]
      rw [hcard]
      have hs : epsilon ≤ d (n + 1) - d n := le_of_lt hn
      push_cast
      nlinarith
    · have hcard :
          ((Finset.range (n + 1)).filter (fun i => epsilon < d (i + 1) - d i)).card =
            ((Finset.range n).filter (fun i => epsilon < d (i + 1) - d i)).card := by
          simp [Finset.range_add_one, Finset.filter_insert, hn, Finset.mem_range]
      rw [hcard]
      have hm : d n ≤ d (n + 1) := hd (Nat.le_succ n)
      nlinarith
