-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb84_shifted_finite_difference_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:54:06.679643+00:00
-- url     : https://prove2.me/submissions/a7cee929-140d-451e-b4e3-58abd3494c08

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Sum of adjacent increments on a shifted finite integer interval. -/
theorem solution (f : ℕ → ℝ) (a b : ℕ) :
    (Finset.range b).sum (fun j => f (a + j + 1) - f (a + j)) =
      f (a + b) - f a := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Nat.add_succ]
      ring
