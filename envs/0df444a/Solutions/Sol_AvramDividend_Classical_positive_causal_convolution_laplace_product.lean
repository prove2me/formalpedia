-- Prove2me | solution 1 for AvramDividend.Classical.positive_causal_convolution_laplace_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T15:11:59.583854+00:00
-- url     : https://prove2.me/submissions/29c322a9-6bec-4350-856e-df625c85a82f

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- The Laplace transform of a signed real causal convolution is the product
of its factor transforms, provided both exponentially weighted factors are L1. -/
theorem solution (f g : ℝ → ℝ) (θ : ℝ)
    (hf : IntegrableOn (fun t : ℝ => Real.exp (-(θ * t)) * f t)
      (Ioi (0 : ℝ)) volume)
    (hg : IntegrableOn (fun t : ℝ => Real.exp (-(θ * t)) * g t)
      (Ioi (0 : ℝ)) volume) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ * x)) *
        (∫ s in Ioc (0 : ℝ) x, f s * g (x - s) ∂volume) ∂volume) =
      (∫ t in Ioi (0 : ℝ), Real.exp (-(θ * t)) * f t ∂volume) *
      (∫ t in Ioi (0 : ℝ), Real.exp (-(θ * t)) * g t ∂volume) := by
  have hconv := MeasureTheory.integral_posConvolution
    hf hg (ContinuousLinearMap.mul ℝ ℝ)
  simp_rw [ContinuousLinearMap.mul_apply'] at hconv
  rw [← hconv]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro x hx
  dsimp only
  rw [intervalIntegral.integral_of_le hx.le]
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc ?_
  intro s hs
  have hfactor :
      Real.exp (-(θ * s)) * Real.exp (-(θ * (x - s))) =
        Real.exp (-(θ * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp (-(θ * x)) * (f s * g (x - s)) =
      (Real.exp (-(θ * s)) * Real.exp (-(θ * (x - s)))) *
        (f s * g (x - s)) := by rw [hfactor]
    _ = (Real.exp (-(θ * s)) * f s) *
        (Real.exp (-(θ * (x - s))) * g (x - s)) := by ring
