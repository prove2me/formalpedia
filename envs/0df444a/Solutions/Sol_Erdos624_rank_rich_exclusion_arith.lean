-- Prove2me | solution 1 for Erdos624.rank_rich_exclusion_arith
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T15:24:41.48725+00:00
-- url     : https://prove2.me/submissions/1b9f5f7a-a156-4c6c-b898-8ead090290ef

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

theorem rank_rich_exclusion_arith (n s : ℕ) (hn : 0 < n) (h1 : n ≤ 64 * s)
    (h2 : s ^ 4 ≤ 2 ^ 132 * n ^ 3) : n ≤ 2 ^ 156 := by
  exact E624R12.rank_rich_arith n s hn h1 h2

end Erdos624

open Finset

theorem solution (n s : ℕ) (hn : 0 < n) (h1 : n ≤ 64 * s)
    (h2 : s ^ 4 ≤ 2 ^ 132 * n ^ 3) : n ≤ 2 ^ 156 :=
  Erdos624.rank_rich_exclusion_arith n s hn h1 h2
