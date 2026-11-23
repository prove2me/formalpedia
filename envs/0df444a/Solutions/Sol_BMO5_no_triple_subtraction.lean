-- Prove2me | solution 1 for BMO5.no_triple_subtraction
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-23T16:54:33.68355+00:00
-- url     : https://prove2.me/submissions/040efbf2-cdf8-44c1-aff0-c673c30c9197

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
    ∀ n, ¬ (10 * 2 ^ (a n) - 1 ≤ b n ∧ 10 * 2 ^ (a (n + 1)) - 1 ≤ b (n + 1) ∧
      10 * 2 ^ (a (n + 2)) - 1 ≤ b (n + 2)) := by
  have inv := BMO5Seq.inv a b a_ini b_ini a_rec b_rec
  intro n ⟨h1, h2, h3⟩
  have h3' : 10 * 2 ^ (a (n + 1 + 1)) - 1 ≤ b (n + 1 + 1) := h3
  have hinv := inv n
  have hlt := BMO5Seq.lt_pow (a n)
  have ha1 : a (n + 1) = a n + 1 := by rw [a_rec, if_pos h1]
  have hb1 : b (n + 1) = b n - (10 * 2 ^ (a n) - 1) := by rw [b_rec, if_pos h1]
  have ha2 : a (n + 1 + 1) = a (n + 1) + 1 := by rw [a_rec, if_pos h2]
  have hb2 : b (n + 1 + 1) = b (n + 1) - (10 * 2 ^ (a (n + 1)) - 1) := by rw [b_rec, if_pos h2]
  rw [ha2, hb2, ha1, hb1] at h3'
  rw [ha1, hb1] at h2
  simp only [pow_succ] at h3'
  simp only [pow_succ] at h2
  have hP : 1 ≤ 2 ^ (a n) := Nat.one_le_two_pow
  clear h3 ha2 hb2
  generalize 2 ^ (a n) = P at *
  omega
