-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_geometric_recursion_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:15:01.136509+00:00
-- url     : https://prove2.me/submissions/0eeb3505-3aa4-44c2-8527-a3aba2f7c827

import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Data.ENNReal.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal

/-! A one-step discounted record expectation upper estimate propagates geometrically. -/
theorem solution (p : ℝ≥0∞) (v : ℕ → ℝ≥0∞)
    (hzero : v 0 ≤ 1) (hstep : ∀ n, v (n + 1) ≤ p * v n) :
    ∀ n, v n ≤ p ^ n := by
  intro n
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
      calc
        v (n + 1) ≤ p * v n := hstep n
        _ ≤ p * p ^ n := mul_le_mul_of_nonneg_left ih (by exact bot_le)
        _ = p ^ (n + 1) := by simp [pow_succ, mul_comm]
