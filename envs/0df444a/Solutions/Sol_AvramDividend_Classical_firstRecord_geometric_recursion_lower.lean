-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_geometric_recursion_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:14:57.472591+00:00
-- url     : https://prove2.me/submissions/d790520d-17eb-4b9b-a557-17bf139cc597

import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Data.ENNReal.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal

/-! A one-step discounted record expectation lower estimate propagates geometrically. -/
theorem solution (p : ℝ≥0∞) (v : ℕ → ℝ≥0∞)
    (hzero : 1 ≤ v 0) (hstep : ∀ n, p * v n ≤ v (n + 1)) :
    ∀ n, p ^ n ≤ v n := by
  intro n
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
      calc
        p ^ (n + 1) = p * p ^ n := by simp [pow_succ, mul_comm]
        _ ≤ p * v n := mul_le_mul_of_nonneg_left ih (by exact bot_le)
        _ ≤ v (n + 1) := hstep n
