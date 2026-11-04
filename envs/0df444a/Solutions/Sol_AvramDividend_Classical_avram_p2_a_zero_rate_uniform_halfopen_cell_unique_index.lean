-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_uniform_halfopen_cell_unique_index
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:03:23.566352+00:00
-- url     : https://prove2.me/submissions/3f6a3120-8405-4d7d-8570-415729d6788b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal

/-- A point can belong to at most one consecutive half-open interval
of a uniform nonnegative grid, including grid-aligned endpoints. -/
theorem solution
    (u δ : ℝ≥0) (i j : ℕ)
    (hi : (i : ℝ≥0) * δ < u ∧
      u ≤ ((i + 1 : ℕ) : ℝ≥0) * δ)
    (hj : (j : ℝ≥0) * δ < u ∧
      u ≤ ((j + 1 : ℕ) : ℝ≥0) * δ) :
    i = j := by
  by_contra hneq
  rcases lt_or_gt_of_ne hneq with hij | hji
  · have hsucc : i + 1 ≤ j := Nat.succ_le_iff.mpr hij
    have hbound : (((i + 1 : ℕ) : ℝ≥0) * δ) ≤ (j : ℝ≥0) * δ := by
      gcongr
    exact (not_lt_of_ge (le_trans hi.2 hbound)) hj.1
  · have hsucc : j + 1 ≤ i := Nat.succ_le_iff.mpr hji
    have hbound : (((j + 1 : ℕ) : ℝ≥0) * δ) ≤ (i : ℝ≥0) * δ := by
      gcongr
    exact (not_lt_of_ge (le_trans hj.2 hbound)) hi.1
