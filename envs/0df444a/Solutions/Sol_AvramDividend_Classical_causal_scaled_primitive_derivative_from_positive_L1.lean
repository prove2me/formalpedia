-- Prove2me | solution 1 for AvramDividend.Classical.causal_scaled_primitive_derivative_from_positive_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T18:52:13.89901+00:00
-- url     : https://prove2.me/submissions/6012a3ca-4255-4791-a5e7-86a575afe39a

import Mathlib.Tactic.FunProp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_positive_L1_intervalIntegrable
import Theorems.Thm_AvramDividend_Classical_causal_exp_weighted_scaled_primitive_hasDerivAt_local
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Positive-time L1 and continuity provide the precise damped primitive derivative. -/
theorem solution
    (P : ℝ → ℝ) (a w : ℝ)
    (hPL1 : IntegrableOn P (Ioi (0 : ℝ)) volume)
    (hPcont : ContinuousOn P (Ioi (0 : ℝ))) :
    ∀ x : ℝ, 0 < x →
      HasDerivAt (fun y : ℝ =>
        (Real.exp (-w * y) *
          (∫ s in Ioc (0 : ℝ) y,
            Real.exp (w * s) * P s ∂volume)) / a)
        (P x / a - w *
          ((Real.exp (-w * x) *
            (∫ s in Ioc (0 : ℝ) x,
              Real.exp (w * s) * P s ∂volume)) / a)) x := by
  have hExp : Continuous (fun s : ℝ => Real.exp (w * s)) := by
    fun_prop
  have hInt : ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun s : ℝ => Real.exp (w * s) * P s)
        volume 0 x := by
    intro x hx
    exact (causal_positive_L1_intervalIntegrable P hPL1 x hx).continuousOn_mul
      hExp.continuousOn
  have hCont : ContinuousOn
      (fun s : ℝ => Real.exp (w * s) * P s) (Ioi (0 : ℝ)) :=
    hExp.continuousOn.mul hPcont
  exact causal_exp_weighted_scaled_primitive_hasDerivAt_local P a w hInt hCont
