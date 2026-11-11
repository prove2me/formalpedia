-- Prove2me | solution 1 for EliasGlobalClock.LowerBound.binary_entropy_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-10T21:29:15.958198+00:00
-- url     : https://prove2.me/submissions/b084d0ef-71cf-4513-b5c4-350bf97d333c

import Mathlib

/-- Fact D.3, printed p.36 / PDF p.37, including x=0 and x=1. -/
theorem solution (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.binEntropy x ≤ 2 * Real.log (Real.sqrt x + Real.sqrt (1 - x)) ∧
    2 * Real.log (Real.sqrt x + Real.sqrt (1 - x)) ≤
      2 * Real.sqrt (x * (1 - x)) := by
  have hy : 0 ≤ 1 - x := by linarith
  set a := Real.sqrt x with ha
  set b := Real.sqrt (1 - x) with hb
  have ha2 : a ^ 2 = x := Real.sq_sqrt hx0
  have hb2 : b ^ 2 = 1 - x := Real.sq_sqrt hy
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hw : Real.sqrt (x * (1 - x)) = a * b := by
    rw [Real.sqrt_mul hx0]
  have hs2 : (a + b) ^ 2 = 1 + 2 * (a * b) := by nlinarith
  have hspos : 0 < a + b := by
    rcases eq_or_lt_of_le ha0 with h | h
    · have : 0 < b := by
        rcases eq_or_lt_of_le hb0 with h' | h'
        · exfalso; nlinarith
        · exact h'
      linarith
    · linarith
  constructor
  · rcases eq_or_lt_of_le hx0 with h0 | h0
    · subst h0
      have : Real.sqrt 0 = 0 := Real.sqrt_zero
      simp [a, b, Real.binEntropy]
    rcases eq_or_lt_of_le hx1 with h1 | h1
    · subst h1
      simp [a, b, Real.binEntropy]
    have hapos : 0 < a := Real.sqrt_pos.mpr h0
    have hbpos : 0 < b := Real.sqrt_pos.mpr (by linarith)
    have key : ∀ c : ℝ, 0 < c → c ^ 2 * Real.log (1 / ((a + b) * c)) ≤ c / (a + b) - c ^ 2 := by
      intro c hc
      have h := Real.log_le_sub_one_of_pos (show 0 < 1 / ((a + b) * c) by positivity)
      have := mul_le_mul_of_nonneg_left h (sq_nonneg c)
      calc _ ≤ c ^ 2 * (1 / ((a + b) * c) - 1) := this
        _ = _ := by field_simp
    have k1 := key a hapos
    have k2 := key b hbpos
    have hla : Real.log a = Real.log x / 2 := by
      rw [ha, Real.log_sqrt hx0]
    have hlb : Real.log b = Real.log (1 - x) / 2 := by
      rw [hb, Real.log_sqrt hy]
    have e1 : Real.log (1 / ((a + b) * a)) = -Real.log (a + b) - Real.log a := by
      rw [one_div, Real.log_inv, Real.log_mul hspos.ne' hapos.ne']; ring
    have e2 : Real.log (1 / ((a + b) * b)) = -Real.log (a + b) - Real.log b := by
      rw [one_div, Real.log_inv, Real.log_mul hspos.ne' hbpos.ne']; ring
    rw [e1] at k1
    rw [e2] at k2
    have hsum : a / (a + b) - a ^ 2 + (b / (a + b) - b ^ 2) = 0 := by
      field_simp; nlinarith
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv]
    rw [hla, ha2] at k1
    rw [hlb, hb2] at k2
    nlinarith
  · have h := Real.log_le_sub_one_of_pos (show 0 < (a + b) ^ 2 by positivity)
    rw [Real.log_pow] at h
    rw [hw]
    push_cast at h
    nlinarith
