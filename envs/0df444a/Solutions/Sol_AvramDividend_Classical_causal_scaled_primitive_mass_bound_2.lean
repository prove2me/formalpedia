-- Prove2me | solution 2 for AvramDividend.Classical.causal_scaled_primitive_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T18:56:43.631229+00:00
-- url     : https://prove2.me/submissions/27b63598-8baf-4892-a7c6-f389386f50aa

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_damped_positive_L1_intervalIntegrable
import Theorems.Thm_AvramDividend_Classical_causal_positive_L1_intervalIntegrable
import Theorems.Thm_AvramDividend_Classical_causal_exponentially_damped_primitive_abs_le_mass_div_a
import Theorems.Thm_AvramDividend_Classical_causal_exponential_primitive_convolution_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral

/-- A geometric envelope mass bounds each scaled Neumann primitive. -/
theorem solution
    (P F : ℝ → ℝ) (a w x M : ℝ)
    (ha : 0 < a) (hw : 0 ≤ w) (hx : 0 < x)
    (hPL1 : IntegrableOn P (Ioi (0 : ℝ)) volume)
    (hFL1 : IntegrableOn F (Ioi (0 : ℝ)) volume)
    (hdom : ∀ s : ℝ, 0 ≤ s → |P s| ≤ F s)
    (hMass : ∫ s in Ioc (0 : ℝ) x, F s ∂volume ≤ M) :
    |(Real.exp (-w * x) *
      (∫ s in Ioc (0 : ℝ) x, Real.exp (w * s) * P s ∂volume)) / a|
      ≤ M / a := by
  have hPint : IntervalIntegrable
      (fun s : ℝ => Real.exp (-w * (x - s)) * P s) volume 0 x :=
    causal_damped_positive_L1_intervalIntegrable P w x hPL1 hx
  have hFint : IntervalIntegrable F volume 0 x :=
    causal_positive_L1_intervalIntegrable F hFL1 x hx
  have hdom' : ∀ s ∈ Ioo (0 : ℝ) x, |P s| ≤ F s := by
    intro s hs
    exact hdom s hs.1.le
  have hMass' : ∫ s in (0 : ℝ)..x, F s ≤ M := by
    simpa only [intervalIntegral.integral_of_le hx.le] using hMass
  have hb := causal_exponentially_damped_primitive_abs_le_mass_div_a
    P F a w x M ha hw hx hPint hFint hdom' hMass'
  have hEq :
      Real.exp (-w * x) *
        (∫ s in Ioc (0 : ℝ) x, Real.exp (w * s) * P s ∂volume) =
      ∫ s in (0 : ℝ)..x, Real.exp (-w * (x - s)) * P s := by
    simpa only [intervalIntegral.integral_of_le hx.le] using
      (causal_exponential_primitive_convolution_identity P w x)
  simpa only [hEq] using hb
