-- Prove2me | solution 1 for AvramDividend.Classical.causal_signed_neumann_undamped_primitive_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T20:55:43.824242+00:00
-- url     : https://prove2.me/submissions/68ac4706-b081-4d6e-8193-2a999fae9edc

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_signed_neumann_power_weighted_primitive_recurrence
import Theorems.Thm_AvramDividend_Classical_causal_exp_damped_signed_kernel_untwist
import Theorems.Thm_AvramDividend_Classical_causal_Ioc_integral_interior_congr

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Untwist each signed convolution power's primitive to the exact Gaussian Volterra kernel. -/
theorem solution
    (a w β : ℝ) (K k : ℝ → ℝ) (P : ℕ → ℝ → ℝ)
    (hk : k = fun t : ℝ =>
      if 0 < t then -(a⁻¹ * Real.exp (-w * t) * (β + K t)) else 0)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hPL1 : ∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume)
    (hPrec : ∀ n : ℕ, P (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, k s * P n (x - s) ∂volume) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      (∫ t in Ioc (0 : ℝ) x,
        Real.exp (w * t) * P (n + 1) t ∂volume) =
      -a⁻¹ * (∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) *
          (∫ t in Ioc (0 : ℝ) s,
            Real.exp (w * t) * P n t ∂volume) ∂volume) := by
  intro n x hx
  have hstep := causal_signed_neumann_power_weighted_primitive_recurrence
    k P w hkL1 hPL1 hPrec n x hx
  calc
    (∫ t in Ioc (0 : ℝ) x,
      Real.exp (w * t) * P (n + 1) t ∂volume) =
      ∫ s in Ioc (0 : ℝ) x,
        (Real.exp (w * (x - s)) * k (x - s)) *
          (∫ t in Ioc (0 : ℝ) s,
            Real.exp (w * t) * P n t ∂volume) ∂volume := hstep
    _ = ∫ s in Ioc (0 : ℝ) x,
      (-a⁻¹ * (β + K (x - s))) *
        (∫ t in Ioc (0 : ℝ) s,
          Real.exp (w * t) * P n t ∂volume) ∂volume := by
          apply causal_Ioc_integral_interior_congr
          intro s hs0 hsx
          rw [hk, causal_exp_damped_signed_kernel_untwist
            a w β K (x - s) (sub_pos.mpr hsx)]
    _ = -a⁻¹ * (∫ s in Ioc (0 : ℝ) x,
      (β + K (x - s)) *
        (∫ t in Ioc (0 : ℝ) s,
          Real.exp (w * t) * P n t ∂volume) ∂volume) := by
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
            ring
