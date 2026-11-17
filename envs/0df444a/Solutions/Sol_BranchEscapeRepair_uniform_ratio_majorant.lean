-- Prove2me | solution 1 for BranchEscapeRepair.uniform_ratio_majorant
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T15:24:31.997304+00:00
-- url     : https://prove2.me/submissions/541d8ae0-83ce-4234-8d86-1a847cc51d04

import Mathlib

namespace BranchEscapeRepair

lemma quadratic_binomial (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    1 + (n : ℝ)*t + ((n : ℝ)*((n : ℝ)-1)/2)*t^2 ≤ (1+t)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hnn : 0 ≤ (n : ℝ)*((n : ℝ)-1) := by
      cases n with
      | zero => norm_num
      | succ k => simp only [Nat.cast_add, Nat.cast_one]; nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have hc : 0 ≤ ((n : ℝ)*((n : ℝ)-1)/2)*t^3 := mul_nonneg (by positivity) (by positivity)
    have hh := mul_le_mul_of_nonneg_right ih (by linarith : 0 ≤ 1+t)
    simp only [Nat.cast_add, Nat.cast_one]
    rw [pow_succ (1+t) n]
    nlinarith

theorem uniform_ratio_majorant (n : ℕ) (hn : 2 ≤ n) (x d : ℝ)
    (hx : 0 < x) (hxn : x ≤ n) (hd : 0 < d) :
    (x / (x+d))^n ≤ 4 / d^2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have ht : 0 ≤ d/x := le_of_lt (div_pos hd hx)
  have hbin := quadratic_binomial n (d/x) ht
  have hxx : 0 < x^2 := sq_pos_of_pos hx
  have hnx : x^2 ≤ (n : ℝ)^2 := sq_le_sq₀ (le_of_lt hx) (by positivity) |>.2 hxn
  have hcoef : (n : ℝ)^2 ≤ 2*((n : ℝ)*((n : ℝ)-1)) := by nlinarith
  have hmain : d^2/4 ≤ ((n : ℝ)*((n : ℝ)-1)/2)*(d/x)^2 := by
    rw [div_pow, ← mul_div_assoc]
    apply (le_div_iff₀ hxx).2
    nlinarith [sq_nonneg d]
  have hpow : d^2/4 ≤ (1+d/x)^n := by
    have : 0 ≤ (n : ℝ)*(d/x) := mul_nonneg (by positivity) ht
    linarith
  have hd2 : 0 < d^2 := sq_pos_of_pos hd
  have hid : x/(x+d) = (1+d/x)⁻¹ := by field_simp
  rw [hid, inv_pow]
  calc
    ((1+d/x)^n)⁻¹ ≤ (d^2/4)⁻¹ := inv_anti₀ (by positivity) hpow
    _ = 4/d^2 := by field_simp

end BranchEscapeRepair
#print axioms BranchEscapeRepair.uniform_ratio_majorant

theorem solution (n : ℕ) (hn : 2 ≤ n) (x d : ℝ)
    (hx : 0 < x) (hxn : x ≤ n) (hd : 0 < d) :
    (x / (x+d))^n ≤ 4 / d^2 :=
  BranchEscapeRepair.uniform_ratio_majorant n hn x d hx hxn hd
#print axioms solution
