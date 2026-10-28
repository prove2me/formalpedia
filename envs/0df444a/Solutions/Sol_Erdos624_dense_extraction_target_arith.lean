-- Prove2me | solution 1 for Erdos624.dense_extraction_target_arith
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T15:24:40.896288+00:00
-- url     : https://prove2.me/submissions/b8cd5142-8cfb-4d60-9444-977c51209de3

import Mathlib
open Finset

namespace E624R12
theorem target_arith (a b n s : ℕ) (hn : 0 < n) (h1 : n ≤ b * s)
    (h2 : s ^ 4 ≤ 2 ^ 104 * a ^ 28 * n ^ 3) : n ≤ 2 ^ 104 * a ^ 28 * b ^ 4 := by
  have h3 : n ^ 4 ≤ (b * s) ^ 4 := Nat.pow_le_pow_left h1 4
  have h4 : n * n ^ 3 ≤ (2 ^ 104 * a ^ 28 * b ^ 4) * n ^ 3 := by
    calc n * n ^ 3 = n ^ 4 := by ring
      _ ≤ (b * s) ^ 4 := h3
      _ = b ^ 4 * s ^ 4 := by ring
      _ ≤ b ^ 4 * (2 ^ 104 * a ^ 28 * n ^ 3) := Nat.mul_le_mul_left _ h2
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right h4 (by positivity)

theorem rank_rich_arith (n s : ℕ) (hn : 0 < n) (h1 : n ≤ 64 * s)
    (h2 : s ^ 4 ≤ 2 ^ 132 * n ^ 3) : n ≤ 2 ^ 156 := by
  have h3 : n ^ 4 ≤ (64 * s) ^ 4 := Nat.pow_le_pow_left h1 4
  have h4 : n * n ^ 3 ≤ 2 ^ 156 * n ^ 3 := by
    calc n * n ^ 3 = n ^ 4 := by ring
      _ ≤ (64 * s) ^ 4 := h3
      _ = 2 ^ 24 * s ^ 4 := by ring
      _ ≤ 2 ^ 24 * (2 ^ 132 * n ^ 3) := Nat.mul_le_mul_left _ h2
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right h4 (by positivity)
end E624R12

namespace Erdos624

theorem dense_extraction_target_arith (a b n s : ℕ) (hn : 0 < n) (h1 : n ≤ b * s)
    (h2 : s ^ 4 ≤ 2 ^ 104 * a ^ 28 * n ^ 3) : n ≤ 2 ^ 104 * a ^ 28 * b ^ 4 := by
  exact E624R12.target_arith a b n s hn h1 h2

end Erdos624

open Finset

theorem solution (a b n s : ℕ) (hn : 0 < n) (h1 : n ≤ b * s)
    (h2 : s ^ 4 ≤ 2 ^ 104 * a ^ 28 * n ^ 3) : n ≤ 2 ^ 104 * a ^ 28 * b ^ 4 :=
  Erdos624.dense_extraction_target_arith a b n s hn h1 h2
