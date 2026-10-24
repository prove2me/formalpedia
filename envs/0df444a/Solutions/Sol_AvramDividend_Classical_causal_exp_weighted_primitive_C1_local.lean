-- Prove2me | solution 1 for AvramDividend.Classical.causal_exp_weighted_primitive_C1_local
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:51:19.686579+00:00
-- url     : https://prove2.me/submissions/48b8ee38-e93d-4bcb-a61a-56af13ba1ff3

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_exp_weighted_primitive_hasDerivAt_local
import Theorems.Thm_AvramDividend_Classical_causal_damped_resolvent_C1_of_continuous_forcing
import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- The local exponentially damped causal primitive is C1 on positive
times when its integrand is locally integrable and continuous. -/
theorem solution
    (g : ℝ → ℝ) (w : ℝ)
    (hInt : ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun s : ℝ => Real.exp (w * s) * g s) volume 0 x)
    (hCont : ContinuousOn (fun s : ℝ => Real.exp (w * s) * g s)
      (Ioi (0 : ℝ)))
    (hgCont : ContinuousOn g (Ioi (0 : ℝ))) :
    ContDiffOn ℝ 1
      (fun y : ℝ => Real.exp (-w * y) *
        (∫ s in Ioc (0 : ℝ) y, Real.exp (w * s) * g s ∂volume))
      (Ioi (0 : ℝ)) := by
  apply causal_damped_resolvent_C1_of_continuous_forcing
    (fun y : ℝ => Real.exp (-w * y) *
      (∫ s in Ioc (0 : ℝ) y, Real.exp (w * s) * g s ∂volume))
    g w hgCont
  intro x hx
  exact causal_exp_weighted_primitive_hasDerivAt_local g w hInt hCont x hx
