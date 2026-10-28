-- Prove2me | solution 1 for AvramDividend.Classical.causal_exp_weighted_scaled_primitive_hasDerivAt_local
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:33:16.128069+00:00
-- url     : https://prove2.me/submissions/fb35c431-1a3e-44a3-a920-13a4cf3d4134

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_exp_weighted_primitive_hasDerivAt_local

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Differentiating an exponentially damped causal primitive commutes with
division by the fixed positive Gaussian Volterra scale coefficient. -/
theorem solution
    (g : ℝ → ℝ) (a w : ℝ)
    (hInt : ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun s : ℝ => Real.exp (w * s) * g s) volume 0 x)
    (hCont : ContinuousOn (fun s : ℝ => Real.exp (w * s) * g s)
      (Ioi (0 : ℝ))) :
    ∀ x : ℝ, 0 < x →
      HasDerivAt (fun y : ℝ =>
        (Real.exp (-w * y) *
          (∫ s in Ioc (0 : ℝ) y,
            Real.exp (w * s) * g s ∂volume)) / a)
        (g x / a - w *
          ((Real.exp (-w * x) *
            (∫ s in Ioc (0 : ℝ) x,
              Real.exp (w * s) * g s ∂volume)) / a)) x := by
  intro x hx
  have hh := causal_exp_weighted_primitive_hasDerivAt_local
    g w hInt hCont x hx
  simpa only [sub_div, mul_div_assoc] using hh.div_const a
