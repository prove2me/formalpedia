-- Prove2me | solution 1 for Esgk.circle_factor_linear_bound
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:49:36.464033+00:00
-- url     : https://prove2.me/submissions/b6e24d7e-845f-4d55-ba44-6e34fe0ca7f1

/-
Standalone solution artifact for Prove2me (mirrors esgk-on3
lean/Esgk/AdditiveExcessArithmetic.lean).-/

import Mathlib

/-- Circle branch (§16.1, (16.1)): a degree-2 factor carries at most 3
points, so `n * 2 ≤ N * (2s)` with `N ≤ 3` forces `n ≤ 3s`. -/
theorem solution (n s N : ℕ) (hN3 : N ≤ 3)
    (hcov : n * 2 ≤ N * (2 * s)) : n ≤ 3 * s := by
  have hle : N * (2 * s) ≤ 3 * (2 * s) :=
    mul_le_mul_of_nonneg_right hN3 (Nat.zero_le _)
  omega


