-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_05_discount_exp_leftLim_eq_rightLim_on_nnreal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:54:21.443674+00:00
-- url     : https://prove2.me/submissions/6c3c0a01-dc4f-4b97-b8f5-816928d6fa28

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal

noncomputable section

/-- Every exponential discount is continuous on nonnegative physical time,
including its bottom endpoint; hence it has no left/right Stieltjes atom. -/
theorem solution
    (q : ℝ) (a : ℝ≥0) :
    Function.leftLim (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ))) a =
      Function.rightLim (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ))) a := by
  let f : ℝ≥0 → ℝ := fun t => Real.exp (-q * (t : ℝ))
  have hcont : Continuous f := by
    dsimp [f]
    exact Real.continuous_exp.comp (by fun_prop)
  have hleft : Function.leftLim f a = f a := by
    apply ContinuousWithinAt.leftLim_eq
    exact hcont.continuousAt.continuousWithinAt
  have hright : Function.rightLim f a = f a := by
    apply ContinuousWithinAt.rightLim_eq
    exact hcont.continuousAt.continuousWithinAt
  exact hleft.trans hright.symm
