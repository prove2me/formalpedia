-- Prove2me | solution 1 for FourExp.zero_count_arith_poly
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-15T03:53:56.461015+00:00
-- url     : https://prove2.me/submissions/51f473e5-76b6-4c61-9a52-23c4fb79b166

import Mathlib

theorem solution
    (n : ℕ) (x lam : ℝ) (hx : 0 ≤ x) (hlam : 0 < lam) (σ : ℕ) (h : σ + 1 ≤ n) :
    (σ : ℝ) < (n : ℝ) / lam + 2 * (1 + (n : ℝ) ^ lam) / (lam * Real.log (n : ℝ)) * (1 + x) := by
  have hn1 : 1 ≤ n := by omega
  have hσn : (σ : ℝ) + 1 ≤ n := by exact_mod_cast h
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hsecond : 0 ≤ 2 * (1 + (n : ℝ) ^ lam) / (lam * Real.log (n : ℝ)) * (1 + x) := by
    have : 0 ≤ (n : ℝ) ^ lam := Real.rpow_nonneg hnpos.le _
    positivity
  by_cases hl : lam ≤ 1
  · have h1 : (n : ℝ) ≤ (n : ℝ) / lam := by
      rw [le_div_iff₀ hlam]
      nlinarith
    linarith
  · push_neg at hl
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have hn : n = 1 := by omega
      have hσ : σ = 0 := by omega
      subst hn; subst hσ
      simp only [Nat.cast_one, Nat.cast_zero, Real.log_one, mul_zero, div_zero, zero_mul, add_zero]
      positivity
    · set L := Real.log (n : ℝ) with hL
      have hLpos : 0 < L := Real.log_pos (by exact_mod_cast hn2)
      set t := lam * L with ht
      have htpos : 0 < t := by positivity
      have htL : L < t := by rw [ht]; nlinarith
      have hrpow : (n : ℝ) ^ lam = Real.exp t := by
        rw [Real.rpow_def_of_pos hnpos, ht, hL, mul_comm]
      have hexp : (n : ℝ) * (1 + (t - L)) ≤ Real.exp t := by
        have h1 := Real.add_one_le_exp (t - L)
        have h2 : Real.exp t = (n : ℝ) * Real.exp (t - L) := by
          rw [Real.exp_sub, hL, Real.exp_log hnpos]; field_simp
        rw [h2]
        nlinarith
      have hlamL : lam * L = t := rfl
      have e1 : (n : ℝ) / lam = (n : ℝ) * L / t := by
        rw [ht]; field_simp
      have hA : 2 * ((n : ℝ) * (1 + (t - L))) / t ≤ 2 * (1 + Real.exp t) / t := by
        apply div_le_div_of_nonneg_right _ htpos.le
        linarith
      have hB : 2 * (1 + Real.exp t) / t ≤ 2 * (1 + Real.exp t) / t * (1 + x) := by
        have : 0 ≤ 2 * (1 + Real.exp t) / t := by positivity
        nlinarith
      have hkey : (n : ℝ) - 1 < (n : ℝ) * L / t + 2 * ((n : ℝ) * (1 + (t - L))) / t := by
        rw [← add_div, lt_div_iff₀ htpos]
        nlinarith
      rw [e1, hrpow]
      linarith
