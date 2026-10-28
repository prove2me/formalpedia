-- Prove2me | solution 1 for AvramDividend.Classical.causal_polynomial_geometric_majorant_conversion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:24:02.241857+00:00
-- url     : https://prove2.me/submissions/dc999983-8879-46ad-8b98-a70c93b696c4

import Mathlib

theorem solution
    (n : ℕ) (A B r : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (A * (n + 1 : ℝ) ^ 2 + B) * r ^ (n + 1) ≤
      (2 * A + B) * ((n : ℝ) ^ 2 + 1) * r ^ n := by
  have hrn : 0 ≤ r ^ n := pow_nonneg hr0 n
  have h1 : r ^ (n + 1) ≤ r ^ n := pow_le_pow_of_le_one hr0 hr1 (Nat.le_succ n)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h2 : A * (n + 1 : ℝ) ^ 2 + B ≤ (2 * A + B) * ((n : ℝ) ^ 2 + 1) := by
    nlinarith [sq_nonneg ((n : ℝ) - 1), mul_nonneg hB (sq_nonneg (n : ℝ)), mul_nonneg hA (sq_nonneg ((n : ℝ) - 1))]
  have h3 : 0 ≤ A * (n + 1 : ℝ) ^ 2 + B := by positivity
  calc (A * (n + 1 : ℝ) ^ 2 + B) * r ^ (n + 1) ≤ (A * (n + 1 : ℝ) ^ 2 + B) * r ^ n :=
        mul_le_mul_of_nonneg_left h1 h3
    _ ≤ _ := mul_le_mul_of_nonneg_right h2 hrn
