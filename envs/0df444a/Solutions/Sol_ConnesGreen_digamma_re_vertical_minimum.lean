-- Prove2me | solution 1 for ConnesGreen.digamma_re_vertical_minimum
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T00:58:06.349535+00:00
-- url     : https://prove2.me/submissions/6f67bda7-4bb4-435a-802c-63a845c7e36c

import Mathlib
import Theorems.Thm_Zeta23_DigammaSeries_hasSum_digamma_series
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex
theorem reciprocal_re_vertical_le (a : ℝ) (ha : 0 < a) (r : ℝ) :
    (1 / ((a : ℂ) + I * r)).re ≤ 1 / a := by
  have hd : 0 < a ^ 2 + r ^ 2 := by nlinarith [sq_nonneg r]
  simp only [one_div, Complex.inv_re, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, mul_zero, zero_sub,
    zero_add, add_zero, neg_zero, Complex.normSq_apply, ← pow_two, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  rw [← one_div]
  change a / (a ^ 2 + r ^ 2) ≤ 1 / a
  apply (div_le_div_iff₀ hd ha).mpr
  nlinarith [sq_nonneg r]

/-- Exact vertical-line minimum from the EXISTING convergent digamma series,
on the open unit real strip containing the original gamma argument. -/
theorem solution (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (r : ℝ) :
    (Complex.digamma (a : ℂ)).re ≤ (Complex.digamma ((a : ℂ) + I * r)).re := by
  have hmem : ∀ s : ℂ, s.re = a → s ∈ Complex.integerComplement := by
    intro s hs
    rintro ⟨k, hk⟩
    have h := congrArg Complex.re hk
    simp only [Complex.intCast_re] at h
    have hk0 : (0 : ℤ) < k := by exact_mod_cast (show (0 : ℝ) < (k : ℝ) from by linarith)
    have hk1 : k < (1 : ℤ) := by exact_mod_cast (show (k : ℝ) < 1 from by linarith)
    omega
  have h0 := (Zeta23.DigammaSeries.hasSum_digamma_series (hmem (a : ℂ) (by simp))).map Complex.reCLM Complex.reCLM.continuous
  have hr := (Zeta23.DigammaSeries.hasSum_digamma_series
    (hmem ((a : ℂ) + I * r) (by simp))).map Complex.reCLM Complex.reCLM.continuous
  have hterm : ∀ n : ℕ,
      (1 / ((n : ℂ) + 1) - 1 / ((a : ℂ) + n + 1)).re ≤
        (1 / ((n : ℂ) + 1) - 1 / (((a : ℂ) + I * r) + n + 1)).re := by
    intro n
    have h := reciprocal_re_vertical_le (a + n + 1) (by positivity) r
    have e0 : (a : ℂ) + n + 1 = ((a + n + 1 : ℝ) : ℂ) := by push_cast; ring
    have er : ((a : ℂ) + I * r) + n + 1 = ((a + n + 1 : ℝ) : ℂ) + I * r := by push_cast; ring
    rw [e0, er]
    simp only [Complex.sub_re, Complex.div_ofReal_re, Complex.one_re] at ⊢
    linarith
  have hs := hasSum_le hterm h0 hr
  have hi := reciprocal_re_vertical_le a ha r
  simp only [Complex.reCLM_apply, Complex.add_re, Complex.ofReal_re,
    Complex.div_ofReal_re, Complex.one_re] at hs
  linarith

