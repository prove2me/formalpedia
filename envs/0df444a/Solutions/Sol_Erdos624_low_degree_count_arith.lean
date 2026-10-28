-- Prove2me | solution 1 for Erdos624.low_degree_count_arith
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T04:39:27.574594+00:00
-- url     : https://prove2.me/submissions/0d7add9e-b7e1-4ae6-a2d8-a129c7285bd3

import Mathlib
open Finset

namespace E624R13D
open Finset

lemma binom_partial (t D : ℕ) (ht : 2 ≤ t) (hD : D ≤ t - 2) :
    (∑ j ∈ range (D + 1), t.choose j) + t + 1 ≤ 2 ^ t := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
  have h1 : ∑ j ∈ range (D + 1), (s + 2).choose j ≤ ∑ j ∈ range (s + 1), (s + 2).choose j :=
    sum_le_sum_of_subset (range_subset_range.2 (by omega))
  have h2 := Nat.sum_range_choose (s + 2)
  rw [sum_range_succ, sum_range_succ, Nat.choose_self] at h2
  have h3 : (s + 2).choose (s + 1) = s + 2 := Nat.choose_succ_self_right (s + 1)
  omega

theorem low_deg (k t D d b : ℕ) (ht : t = Nat.log 2 k) (ht2 : 2 ≤ t) (hD : D ≤ t - 2)
    (hd : d ≤ t + 1) (hb : 0 < b) :
    (∑ j ∈ range (D + 1), t.choose j) + d ≤ 2 ^ t ∧ 2 ^ t ≤ k ∧
      b * (2 ^ ((∑ j ∈ range (D + 1), t.choose j) + d) - 1) * 2 ^ (t + 1) < b * 2 ^ d * 2 ^ k ∧
      b * (2 ^ ((∑ j ∈ range (D + 1), t.choose j) + d) - 1) * k < b * 2 ^ d * 2 ^ k := by
  set R := ∑ j ∈ range (D + 1), t.choose j
  have hR := binom_partial t D ht2 hD
  have hk0 : k ≠ 0 := by
    intro h; rw [h] at ht; simp at ht; omega
  have htk : 2 ^ t ≤ k := ht ▸ Nat.pow_log_le_self 2 hk0
  have hkt : k < 2 ^ (t + 1) := ht ▸ Nat.lt_pow_succ_log_self (by norm_num) k
  have htk' : t < 2 ^ t := Nat.lt_two_pow_self
  have key : 2 ^ (R + d) * 2 ^ (t + 1) ≤ 2 ^ d * 2 ^ k := by
    rw [← pow_add, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpos : 0 < 2 ^ (R + d) := by positivity
  have h3 : b * (2 ^ (R + d) - 1) * 2 ^ (t + 1) < b * 2 ^ d * 2 ^ k := by
    have : (2 ^ (R + d) - 1) * 2 ^ (t + 1) < 2 ^ d * 2 ^ k := by
      have h' : (2 ^ (R + d) - 1) * 2 ^ (t + 1) < 2 ^ (R + d) * 2 ^ (t + 1) :=
        Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
      omega
    calc b * (2 ^ (R + d) - 1) * 2 ^ (t + 1) = b * ((2 ^ (R + d) - 1) * 2 ^ (t + 1)) := by ring
      _ < b * (2 ^ d * 2 ^ k) := Nat.mul_lt_mul_of_pos_left this hb
      _ = b * 2 ^ d * 2 ^ k := by ring
  refine ⟨by omega, htk, h3, lt_of_le_of_lt ?_ h3⟩
  exact Nat.mul_le_mul_left _ hkt.le

theorem low_deg_256 (k D : ℕ) (hk : 256 ≤ k) (hD : D ≤ Nat.log 2 k - 2) :
    64 * (2 * (2 ^ ((∑ j ∈ range (D + 1), (Nat.log 2 k).choose j) + 2) - 1)) < 2 ^ k := by
  have ht8 : 8 ≤ Nat.log 2 k := Nat.le_log_of_pow_le (by norm_num) (by simpa using hk)
  obtain ⟨-, -, h3, -⟩ := low_deg k (Nat.log 2 k) D 2 2 rfl (by omega) hD (by omega) (by norm_num)
  have h9 : 2 ^ 9 ≤ 2 ^ (Nat.log 2 k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  set X := 2 * (2 ^ ((∑ j ∈ range (D + 1), (Nat.log 2 k).choose j) + 2) - 1)
  have : X * 2 ^ 9 ≤ X * 2 ^ (Nat.log 2 k + 1) := Nat.mul_le_mul_left _ h9
  omega

end E624R13D

namespace Erdos624

theorem low_degree_count_arith (k t D d b : ℕ) (ht : t = Nat.log 2 k) (ht2 : 2 ≤ t)
    (hD : D ≤ t - 2) (hd : d ≤ t + 1) (hb : 0 < b) :
    (∑ j ∈ Finset.range (D + 1), t.choose j) + d ≤ 2 ^ t ∧ 2 ^ t ≤ k ∧
      b * (2 ^ ((∑ j ∈ Finset.range (D + 1), t.choose j) + d) - 1) * 2 ^ (t + 1) <
        b * 2 ^ d * 2 ^ k ∧
      b * (2 ^ ((∑ j ∈ Finset.range (D + 1), t.choose j) + d) - 1) * k < b * 2 ^ d * 2 ^ k := by
  exact E624R13D.low_deg k t D d b ht ht2 hD hd hb

end Erdos624

open Finset

theorem solution (k t D d b : ℕ) (ht : t = Nat.log 2 k) (ht2 : 2 ≤ t)
    (hD : D ≤ t - 2) (hd : d ≤ t + 1) (hb : 0 < b) :
    (∑ j ∈ Finset.range (D + 1), t.choose j) + d ≤ 2 ^ t ∧ 2 ^ t ≤ k ∧
      b * (2 ^ ((∑ j ∈ Finset.range (D + 1), t.choose j) + d) - 1) * 2 ^ (t + 1) <
        b * 2 ^ d * 2 ^ k ∧
      b * (2 ^ ((∑ j ∈ Finset.range (D + 1), t.choose j) + d) - 1) * k < b * 2 ^ d * 2 ^ k :=
  Erdos624.low_degree_count_arith k t D d b ht ht2 hD hd hb
