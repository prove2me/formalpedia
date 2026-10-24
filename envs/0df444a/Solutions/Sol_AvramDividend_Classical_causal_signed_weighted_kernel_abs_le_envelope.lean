-- Prove2me | solution 1 for AvramDividend.Classical.causal_signed_weighted_kernel_abs_le_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T12:04:50.848591+00:00
-- url     : https://prove2.me/submissions/c4026729-d90e-43c4-b266-cbfe44021731

import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- The signed damped resolvent kernel is pointwise bounded by its positive envelope. -/
theorem solution
    (K : ℝ → ℝ) (w β a t : ℝ) (ha : 0 < a) (hK : 0 ≤ K t) :
    |a⁻¹ * Real.exp (-w * t) * (β + K t)| ≤
      a⁻¹ * Real.exp (-w * t) * (|β| + K t) := by
  have hc : 0 ≤ a⁻¹ * Real.exp (-w * t) :=
    mul_nonneg (inv_nonneg.mpr ha.le) (Real.exp_nonneg _)
  calc
    |a⁻¹ * Real.exp (-w * t) * (β + K t)|
        = (a⁻¹ * Real.exp (-w * t)) * |β + K t| := by
          rw [abs_mul, abs_of_nonneg hc]
    _ ≤ (a⁻¹ * Real.exp (-w * t)) * (|β| + K t) := by
          apply mul_le_mul_of_nonneg_left _ hc
          simpa only [abs_of_nonneg hK] using (abs_add_le β (K t))
