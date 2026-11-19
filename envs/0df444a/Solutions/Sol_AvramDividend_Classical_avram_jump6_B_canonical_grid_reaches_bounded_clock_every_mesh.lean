-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_canonical_grid_reaches_bounded_clock_every_mesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T20:30:29.220479+00:00
-- url     : https://prove2.me/submissions/d47cf066-c7f6-4e28-a285-6cc89904d561

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Pointwise
import Mathlib.Topology.Defs.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped NNReal
noncomputable section

theorem solution
    (n j : ℕ) (t : ℝ≥0) (ht : t ≤ (n : ℝ≥0)) :
    t ≤ (((n + 1) * (j + 1) : ℕ) : ℝ≥0) /
      (((j + 1 : ℕ) : ℝ≥0)) := by
  have hj : (0 : ℝ≥0) < ((j + 1 : ℕ) : ℝ≥0) := by
    exact_mod_cast Nat.succ_pos j
  apply (le_div_iff₀ hj).2
  rw [Nat.cast_mul]
  have hn : (n : ℝ≥0) ≤ (((n + 1 : ℕ) : ℝ≥0)) := by
    exact_mod_cast Nat.le_succ n
  exact mul_le_mul_of_nonneg_right (ht.trans hn) (by exact zero_le)
