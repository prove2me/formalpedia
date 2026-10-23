-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_truncated_double_tail_area_uniform_quadratic_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T11:55:42.60666+00:00
-- url     : https://prove2.me/submissions/89a946b6-0d46-42e7-8023-64f0b1bbf1a1

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A quadratic square-completion bounds the truncated double-tail area uniformly. -/
theorem solution (R z : ℝ) :
    z * min R z - (min R z) ^ 2 / 2 ≤ z ^ 2 / 2 := by
  have hsq : 0 ≤ (z - min R z) ^ 2 := sq_nonneg _
  nlinarith only [hsq]
