-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_right_closed_grid_cell_locator_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:00:09.480193+00:00
-- url     : https://prove2.me/submissions/9bf828ab-975c-416e-ae40-246143ec7cd9

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal

/-- A positive time belongs to at most one right-closed, left-open
uniform cell, including exact mesh-endpoint jump times. -/
theorem solution
    (δ u : ℝ≥0) (i j : ℕ)
    (hiL : (i : ℝ≥0) * δ < u)
    (hiR : u ≤ ((i + 1 : ℕ) : ℝ≥0) * δ)
    (hjL : (j : ℝ≥0) * δ < u)
    (hjR : u ≤ ((j + 1 : ℕ) : ℝ≥0) * δ) :
    i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hc : ((i + 1 : ℕ) : ℝ≥0) ≤ (j : ℝ≥0) := by
      exact_mod_cast Nat.succ_le_of_lt hij
    have hm : ((i + 1 : ℕ) : ℝ≥0) * δ ≤ (j : ℝ≥0) * δ :=
      mul_le_mul_of_nonneg_right hc (show (0 : ℝ≥0) ≤ δ from zero_le)
    exact (not_lt_of_ge (le_trans hiR hm)) hjL
  · have hc : ((j + 1 : ℕ) : ℝ≥0) ≤ (i : ℝ≥0) := by
      exact_mod_cast Nat.succ_le_of_lt hji
    have hm : ((j + 1 : ℕ) : ℝ≥0) * δ ≤ (i : ℝ≥0) * δ :=
      mul_le_mul_of_nonneg_right hc (show (0 : ℝ≥0) ≤ δ from zero_le)
    exact (not_lt_of_ge (le_trans hjR hm)) hiL