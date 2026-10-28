-- Prove2me | solution 1 for AvramDividend.Classical.causal_damped_primitive_Ioc_convolution_scaled
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T18:12:20.014034+00:00
-- url     : https://prove2.me/submissions/35f9c66a-3b31-4336-8d86-40f3f75c3ff0

import Mathlib
open MeasureTheory Set intervalIntegral
theorem solution
    (P : ℝ → ℝ) (a w x : ℝ) (hx : 0 ≤ x) :
    (Real.exp (-w * x) *
      (∫ s in Ioc (0 : ℝ) x, Real.exp (w * s) * P s ∂volume)) / a =
    ∫ s in Ioc (0 : ℝ) x,
      P (x - s) * (Real.exp (-w * s) / a) ∂volume := by
  rw [← integral_of_le hx, ← integral_of_le hx]
  have h := intervalIntegral.integral_comp_sub_left
    (fun s => P s * (Real.exp (-w * (x - s)) / a)) (a := 0) (b := x) x
  simp only [sub_sub_cancel, sub_self, sub_zero] at h
  rw [h, ← intervalIntegral.integral_const_mul, div_eq_mul_inv, mul_comm _ a⁻¹,
    ← intervalIntegral.integral_const_mul]
  congr 1; ext s
  rw [show -w * (x - s) = -w * x + w * s by ring, Real.exp_add]
  ring
