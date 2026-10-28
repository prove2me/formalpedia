-- Prove2me | solution 1 for AvramDividend.Classical.causal_monotone_C1_globalL1_convolution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:43:21.821776+00:00
-- url     : https://prove2.me/submissions/7571a9f2-0a69-48a7-8a96-1e155d7d8289

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_monotone_C1_kernel_derivative_primitive_from_zero
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_C1_of_kernel_primitive
import Theorems.Thm_AvramDividend_Classical_causal_convolution_time_reversal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
theorem solution
    (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Ici (0 : ℝ)))
    (hfL1 : IntegrableOn f (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (hg0 : g 0 = 0)
    (hgmono : MonotoneOn g (Ici (0 : ℝ)))
    (hgC1 : ContDiffOn ℝ 1 g (Ioi (0 : ℝ)))
    (hgderivL1 : IntegrableOn (deriv g) (Ioi (0 : ℝ)) volume) :
    ContDiffOn ℝ 1
      (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
        f s * g (x - s) ∂volume) (Ioi (0 : ℝ)) := by
  have hprimitive (x : ℝ) (hx : 0 < x) :
      (∫ t in Ioc (0 : ℝ) x, deriv g t ∂volume) = g x := by
    obtain ⟨_, hftc⟩ :=
      monotone_C1_kernel_derivative_primitive_from_zero
        g hg0 hg hgmono hgC1 x hx
    rw [← intervalIntegral.integral_of_le (le_of_lt hx)]
    exact hftc
  have hc1 :=
    causal_l1_convolution_C1_of_kernel_primitive
      f (deriv g) g hf hfL1 hgderivL1 hprimitive
  apply hc1.congr
  intro x hx
  have hxf : 0 ≤ x := le_of_lt hx
  calc
    (∫ s in Ioc (0 : ℝ) x, f s * g (x - s) ∂volume) =
        (∫ s in Ioc (0 : ℝ) x, g (x - s) * f s ∂volume) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with s
          exact mul_comm _ _
    _ = (∫ s in Ioc (0 : ℝ) x, g s * f (x - s) ∂volume) :=
          causal_convolution_time_reversal g f x hxf
    _ = (∫ s in Ioc (0 : ℝ) x, f (x - s) * g s ∂volume) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with s
          exact mul_comm _ _
