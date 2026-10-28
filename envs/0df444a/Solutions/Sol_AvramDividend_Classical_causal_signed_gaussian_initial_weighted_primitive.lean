-- Prove2me | solution 1 for AvramDividend.Classical.causal_signed_gaussian_initial_weighted_primitive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T20:56:10.516355+00:00
-- url     : https://prove2.me/submissions/c20ec2bf-94aa-4722-b341-03f61c133026

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_causal_exp_damped_signed_kernel_untwist
import Theorems.Thm_AvramDividend_Classical_causal_Ioc_integral_interior_congr

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- The initial Gaussian Neumann primitive is the undamped kernel's integral. -/
theorem solution
    (a w β : ℝ) (K k : ℝ → ℝ)
    (hk : k = fun t : ℝ =>
      if 0 < t then -(a⁻¹ * Real.exp (-w * t) * (β + K t)) else 0)
    (x : ℝ) :
    (∫ s in Ioc (0 : ℝ) x, Real.exp (w * s) * k s ∂volume) =
      -a⁻¹ * (∫ s in Ioc (0 : ℝ) x, β + K s ∂volume) := by
  calc
    (∫ s in Ioc (0 : ℝ) x, Real.exp (w * s) * k s ∂volume) =
      (∫ s in Ioc (0 : ℝ) x, -a⁻¹ * (β + K s) ∂volume) := by
        apply causal_Ioc_integral_interior_congr
        intro s hs0 hsx
        rw [hk, causal_exp_damped_signed_kernel_untwist a w β K s hs0]
    _ = -a⁻¹ * (∫ s in Ioc (0 : ℝ) x, β + K s ∂volume) := by
      rw [← integral_const_mul]
