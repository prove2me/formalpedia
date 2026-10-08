-- Prove2me | solution 1 for AvramDividend.Classical.excursion_laplace_upper_bound_from_support_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:19:19.669266+00:00
-- url     : https://prove2.me/submissions/e5ec0f33-8635-4e41-81c3-79ed2560ce8d

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (β : Measure ℝ) [IsFiniteMeasure β]
    (x θ : ℝ) (hθ : 0 ≤ θ)
    (hsupport : ∀ᵐ y : ℝ ∂β, x ≤ y)
    (hint : Integrable (fun y : ℝ => Real.exp (-(θ * y))) β) :
    (∫ y : ℝ, Real.exp (-(θ * y)) ∂β) ≤
      β.real univ * Real.exp (-(θ * x)) := by
  have hdom : ∀ᵐ y : ℝ ∂β,
      Real.exp (-(θ * y)) ≤ Real.exp (-(θ * x)) := by
    filter_upwards [hsupport] with y hy
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hθ (sub_nonneg.mpr hy)]
  have hconst : Integrable (fun _ : ℝ => Real.exp (-(θ * x))) β :=
    integrable_const _
  have hi := integral_mono_ae hint hconst hdom
  simpa only [integral_const, smul_eq_mul] using hi
