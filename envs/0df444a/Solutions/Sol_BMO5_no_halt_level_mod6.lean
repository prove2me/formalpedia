-- Prove2me | solution 1 for BMO5.no_halt_level_mod6
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-23T16:54:32.563532+00:00
-- url     : https://prove2.me/submissions/87828826-82f2-4d94-831e-f28eaa9edb44

import Mathlib

namespace BMO5Seq

theorem lt_pow (x : ℕ) : x < 2 ^ x := by
  induction x with
  | zero => norm_num
  | succ x ih => rw [pow_succ]; omega

theorem pow_mod3 (x : ℕ) : (2 ^ x % 3 = 1 ∧ x % 2 = 0) ∨ (2 ^ x % 3 = 2 ∧ x % 2 = 1) := by
  induction x with
  | zero => left; norm_num
  | succ x ih => rw [pow_succ]; omega

theorem inv (a b : ℕ → ℕ) (a_ini : a 0 = 0) (b_ini : b 0 = 5)
    (a_rec : ∀ n, a (n + 1) = if 10 * 2 ^ (a n) - 1 ≤ b n then a n + 1 else a n)
    (b_rec : ∀ n, b (n + 1) = if 10 * 2 ^ (a n) - 1 ≤ b n then b n - (10 * 2 ^ (a n) - 1)
      else 3 * b n + a n + 5) :
    ∀ n, 2 * b n + a n + 5 < 3 * (20 * 2 ^ (a n) + a n + 3) := by
  intro n
  induction n with
  | zero => rw [a_ini, b_ini]; norm_num
  | succ n ih =>
    have hP : 1 ≤ 2 ^ (a n) := Nat.one_le_two_pow
    by_cases h : 10 * 2 ^ (a n) - 1 ≤ b n
    · rw [a_rec, b_rec, if_pos h, if_pos h, pow_succ]
      generalize 2 ^ (a n) = P at *
      omega
    · rw [a_rec, b_rec, if_neg h, if_neg h]
      generalize 2 ^ (a n) = P at *
      omega

end BMO5Seq

theorem solution (a b : ℕ → ℕ) (a_ini : a 0 = 0) (b_ini : b 0 = 5)
    (a_rec : ∀ n, a (n + 1) = if 10 * 2 ^ (a n) - 1 ≤ b n then a n + 1 else a n)
    (b_rec : ∀ n, b (n + 1) = if 10 * 2 ^ (a n) - 1 ≤ b n then b n - (10 * 2 ^ (a n) - 1)
      else 3 * b n + a n + 5) :
    ∀ n, (a n % 6 = 3 ∨ a n % 6 = 4) → b n ≠ 10 * 2 ^ (a n) - 2 := by
  have inv := BMO5Seq.inv a b a_ini b_ini a_rec b_rec
  intro n hi hb
  cases n with
  | zero => rw [a_ini] at hi; omega
  | succ m =>
    by_cases h1 : 10 * 2 ^ (a m) - 1 ≤ b m
    · have ha1 : a (m + 1) = a m + 1 := by rw [a_rec, if_pos h1]
      have hb1 : b (m + 1) = b m - (10 * 2 ^ (a m) - 1) := by rw [b_rec, if_pos h1]
      rw [ha1] at hi hb
      rw [hb1] at hb
      cases m with
      | zero => rw [a_ini] at hi; omega
      | succ p =>
        by_cases h2 : 10 * 2 ^ (a p) - 1 ≤ b p
        · have ha2 : a (p + 1) = a p + 1 := by rw [a_rec, if_pos h2]
          have hb2 : b (p + 1) = b p - (10 * 2 ^ (a p) - 1) := by rw [b_rec, if_pos h2]
          have hinv := inv p
          have hlt := BMO5Seq.lt_pow (a p)
          rw [ha2] at hi hb h1
          rw [hb2] at hb h1
          simp only [pow_succ] at hb
          simp only [pow_succ] at h1
          have hP : 1 ≤ 2 ^ (a p) := Nat.one_le_two_pow
          generalize 2 ^ (a p) = P at *
          omega
        · have ha2 : a (p + 1) = a p := by rw [a_rec, if_neg h2]
          have hb2 : b (p + 1) = 3 * b p + a p + 5 := by rw [b_rec, if_neg h2]
          rw [ha2] at hi hb h1
          rw [hb2] at hb h1
          simp only [pow_succ] at hb
          have hP : 1 ≤ 2 ^ (a p) := Nat.one_le_two_pow
          generalize 2 ^ (a p) = P at *
          omega
    · have ha1 : a (m + 1) = a m := by rw [a_rec, if_neg h1]
      have hb1 : b (m + 1) = 3 * b m + a m + 5 := by rw [b_rec, if_neg h1]
      rw [ha1] at hi hb
      rw [hb1] at hb
      have h3 := BMO5Seq.pow_mod3 (a m)
      have hP : 1 ≤ 2 ^ (a m) := Nat.one_le_two_pow
      generalize 2 ^ (a m) = P at *
      omega
