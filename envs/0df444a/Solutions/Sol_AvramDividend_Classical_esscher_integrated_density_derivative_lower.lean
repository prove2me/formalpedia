-- Prove2me | solution 1 for AvramDividend.Classical.esscher_integrated_density_derivative_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:25:36.266313+00:00
-- url     : https://prove2.me/submissions/d5c7f3ed-17e6-4277-aef6-d2b20e6072e2

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory intervalIntegral Filter
open scoped Topology

/-- Full analytic proof: FTC followed by the product rule and positivity. -/
theorem solution
    (φ c x : ℝ) (f : ℝ → ℝ) (k : ℝ)
    (hφ : 0 ≤ φ) (hx : 0 ≤ x)
    (hint : IntervalIntegrable f volume 0 x)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 x) volume)
    (hcont : ContinuousAt f x)
    (hFnonneg : 0 ≤ c + ∫ t in (0 : ℝ)..x, f t)
    (hfnonneg : 0 ≤ f x) (hk : k ≤ f x) :
    k ≤ deriv
      (fun y : ℝ => Real.exp (φ * y) *
        (c + ∫ t in (0 : ℝ)..y, f t)) x := by
  have hlin : HasDerivAt (fun y : ℝ => φ * y) φ x := by
    simpa using (hasDerivAt_id x).const_mul φ
  have hexp := hlin.exp
  have hint_deriv :
      HasDerivAt (fun y : ℝ => ∫ t in (0 : ℝ)..y, f t) (f x) x :=
    intervalIntegral.integral_hasDerivAt_right hint hmeas hcont
  have hsum :
      HasDerivAt (fun y : ℝ => c + ∫ t in (0 : ℝ)..y, f t) (f x) x := by
    exact hint_deriv.const_add c
  have hformula :
      deriv (fun y : ℝ => Real.exp (φ * y) *
        (c + ∫ t in (0 : ℝ)..y, f t)) x =
        (Real.exp (φ * x) * φ) *
          (c + ∫ t in (0 : ℝ)..x, f t) +
        Real.exp (φ * x) * f x := (hexp.mul hsum).deriv
  have he : (1 : ℝ) ≤ Real.exp (φ * x) := by
    have hbound := Real.add_one_le_exp (φ * x)
    have hprod : 0 ≤ φ * x := mul_nonneg hφ hx
    linarith
  have hfirst : 0 ≤
      (Real.exp (φ * x) * φ) *
        (c + ∫ t in (0 : ℝ)..x, f t) :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le hφ) hFnonneg
  have hsecond : f x ≤ Real.exp (φ * x) * f x := by
    simpa using (mul_le_mul_of_nonneg_right he hfnonneg)
  rw [hformula]
  linarith
