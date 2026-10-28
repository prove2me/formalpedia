-- Prove2me | solution 2 for AvramDividend.Classical.causal_exponential_tsum_untwist
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T21:02:05.12374+00:00
-- url     : https://prove2.me/submissions/9e6373ca-72ee-46ca-b236-85788051b80a

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real

/-- Exponential weights cancel through a real infinite series, even without summability. -/
theorem solution
    (A : ℕ → ℝ) (w x a : ℝ) :
    Real.exp (w * x) *
      (∑' n : ℕ, (Real.exp (-w * x) * A n) / a) =
        (∑' n : ℕ, A n / a) := by
  have he : Real.exp (w * x) * Real.exp (-w * x) = 1 := by
    rw [← Real.exp_add]
    have hz : w * x + -w * x = 0 := by ring
    rw [hz, Real.exp_zero]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  calc
    Real.exp (w * x) * ((Real.exp (-w * x) * A n) / a) =
      (Real.exp (w * x) * Real.exp (-w * x)) * A n / a := by ring
    _ = A n / a := by rw [he]; ring
