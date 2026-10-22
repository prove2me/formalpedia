-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_atom_lipschitz_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T18:23:56.444692+00:00
-- url     : https://prove2.me/submissions/0b26ac24-6cbd-4e84-b90a-15056f6d1c7e

import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The positive-part double-tail atom is Lipschitz in time,
with Esscher-weighted constant exp(-φz). -/
theorem solution (φ z s t : ℝ) :
    |max (z - t) 0 * Real.exp (-φ * z) -
      max (z - s) 0 * Real.exp (-φ * z)| ≤
      |t - s| * Real.exp (-φ * z) := by
  have hmax :
      |max (z - t) 0 - max (z - s) 0| ≤ |t - s| := by
    calc
      |max (z - t) 0 - max (z - s) 0| ≤
          |(z - t) - (z - s)| :=
        abs_max_sub_max_le_abs _ _ _
      _ = |t - s| := by
        have h : (z - t) - (z - s) = s - t := by ring
        rw [h, abs_sub_comm]
  rw [← sub_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right hmax (Real.exp_pos _).le
