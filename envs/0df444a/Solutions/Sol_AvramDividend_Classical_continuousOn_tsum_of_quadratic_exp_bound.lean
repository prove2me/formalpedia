-- Prove2me | solution 1 for AvramDividend.Classical.continuousOn_tsum_of_quadratic_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:57:59.017586+00:00
-- url     : https://prove2.me/submissions/b06191b4-ee83-4daa-af90-c0d1d2df7c50

import Mathlib
set_option autoImplicit false
open Set

theorem solution
    (f : ℕ → ℝ → ℝ) (K : Set ℝ) (C r : ℝ) (hr : 0 < r)
    (hf : ∀ n : ℕ, ContinuousOn (f n) K)
    (hbound : ∀ n : ℕ, ∀ x ∈ K,
      ‖f n x‖ ≤ C * ((n : ℝ) ^ 2 * Real.exp (-r * (n : ℝ)))) :
    ContinuousOn (fun x : ℝ => ∑' n : ℕ, f n x) K := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ 2 * Real.exp (-r * (n : ℝ))) :=
    Real.summable_pow_mul_exp_neg_nat_mul 2 hr
  exact continuousOn_tsum hf (hs.mul_left C) hbound
