-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_monotone_marked_grid_index_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:04:20.961037+00:00
-- url     : https://prove2.me/submissions/59365da5-d879-44cc-a469-7033ba50888d

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal

/-- An original marked time lies in at most one right-closed monotone grid cell. -/
theorem solution
    (grid : ℕ → ℝ≥0) (hmono : Monotone grid)
    (u : ℝ≥0) (i j : ℕ)
    (hi : u ∈ Set.Ioc (grid i) (grid (i + 1)))
    (hj : u ∈ Set.Ioc (grid j) (grid (j + 1))) :
    i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hle : grid (i + 1) ≤ grid j := hmono (by omega)
    have hui : u ≤ grid (i + 1) := (Set.mem_Ioc.mp hi).2
    have huj : grid j < u := (Set.mem_Ioc.mp hj).1
    exact (not_lt_of_ge (le_trans hui hle)) huj
  · have hle : grid (j + 1) ≤ grid i := hmono (by omega)
    have huj : u ≤ grid (j + 1) := (Set.mem_Ioc.mp hj).2
    have hui : grid i < u := (Set.mem_Ioc.mp hi).1
    exact (not_lt_of_ge (le_trans huj hle)) hui
