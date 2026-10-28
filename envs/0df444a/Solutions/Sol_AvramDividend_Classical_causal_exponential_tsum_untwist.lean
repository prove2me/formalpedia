-- Prove2me | solution 1 for AvramDividend.Classical.causal_exponential_tsum_untwist
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T21:01:27.557186+00:00
-- url     : https://prove2.me/submissions/4fde47a4-615d-44ec-a209-426273750220

import Mathlib

open Real

theorem solution
    (A : ℕ → ℝ) (w x a : ℝ) :
    Real.exp (w * x) *
      (∑' n : ℕ, (Real.exp (-w * x) * A n) / a) =
        (∑' n : ℕ, A n / a) := by
  have h : ∀ n, (Real.exp (-w * x) * A n) / a = Real.exp (-w * x) * (A n / a) := fun n => by ring
  simp_rw [h]
  rw [tsum_mul_left, ← mul_assoc, ← Real.exp_add]
  rw [show w * x + -w * x = 0 by ring, Real.exp_zero, one_mul]
