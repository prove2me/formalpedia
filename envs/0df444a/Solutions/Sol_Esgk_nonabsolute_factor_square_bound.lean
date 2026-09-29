-- Prove2me | solution 1 for Esgk.nonabsolute_factor_square_bound
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:50:56.476837+00:00
-- url     : https://prove2.me/submissions/71d50495-4904-4e59-b316-0a21fd463b84

/-
Standalone solution artifact for Prove2me (mirrors esgk-on3
lean/Esgk/AdditiveExcessArithmetic.lean).-/

import Mathlib

/-- Nonabsolute branch (§16.2, (16.3)): with `4N ≤ d^2` (Bézout),
coverage `n * d ≤ N * (2s)` and `d ≤ 2s` force `n ≤ s * s`. -/
theorem solution (n s N d : ℕ) (hd1 : 1 ≤ d) (h4N : 4 * N ≤ d ^ 2)
    (hcov : n * d ≤ N * (2 * s)) (hds : d ≤ 2 * s) : n ≤ s * s := by
  have eA : 4 * (n * d) ≤ 4 * (N * (2 * s)) :=
    mul_le_mul_of_nonneg_left hcov (Nat.zero_le _)
  have eB : 4 * (N * (2 * s)) = (2 * s) * (4 * N) := by ring
  have eC : (2 * s) * (4 * N) ≤ (2 * s) * (d ^ 2) :=
    mul_le_mul_of_nonneg_left h4N (Nat.zero_le _)
  have e5 : 4 * n * d ≤ (2 * s * d) * d := by
    have r1 : 4 * n * d = 4 * (n * d) := by ring
    have r2 : (2 * s * d) * d = (2 * s) * (d ^ 2) := by ring
    omega
  have e6 : 4 * n ≤ 2 * s * d := by
    by_contra hc
    have hc' : 2 * s * d < 4 * n := lt_of_not_ge hc
    have hlt : (2 * s * d) * d < (4 * n) * d :=
      mul_lt_mul_of_pos_right hc' (by omega : 0 < d)
    omega
  have e7 : 2 * s * d ≤ 2 * s * (2 * s) :=
    mul_le_mul_of_nonneg_left hds (Nat.zero_le _)
  have r3 : 2 * s * (2 * s) = 4 * (s * s) := by ring
  omega


