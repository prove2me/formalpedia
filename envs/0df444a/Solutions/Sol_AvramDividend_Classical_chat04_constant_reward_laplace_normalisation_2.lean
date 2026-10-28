-- Prove2me | solution 2 for AvramDividend.Classical.chat04_constant_reward_laplace_normalisation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:50:44.158389+00:00
-- url     : https://prove2.me/submissions/e4dfef22-02b8-4a51-bbe7-ff363bb4ff07

import Theorems.Thm_AvramDividend_Classical_chat04_positive_discount_exponential_halfline_integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open AvramDividend.Classical MeasureTheory Set
theorem solution (p c : ℝ) (hp : 0 < p) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * c) = c / p := by 
  have h := integral_exp_mul_Ioi (a := -p) (by linarith) 0
  simp only [mul_zero, Real.exp_zero, zero_sub] at h
  have e : (fun t : ℝ => Real.exp (-(p * t)) * c) = fun t => c * Real.exp (-p * t) := by
    ext t; ring_nf
  rw [e, integral_const_mul, h]; field_simp
