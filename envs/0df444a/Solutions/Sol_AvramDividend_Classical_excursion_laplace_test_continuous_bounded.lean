-- Prove2me | solution 1 for AvramDividend.Classical.excursion_laplace_test_continuous_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:55:09.734954+00:00
-- url     : https://prove2.me/submissions/fe79b5d0-1a2a-4070-b4fe-8e8809aa21f5

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp

/-!
A Laplace test cut off at the origin is continuous, positive and
uniformly bounded by one. It is therefore a valid weak-limit
test for finite measures supported on the nonnegative half-line.
-/
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (s : ℝ) (hs : 0 ≤ s) :
    Continuous (fun x : ℝ => Real.exp (-(s * max x 0))) ∧
      ∀ x : ℝ, 0 < Real.exp (-(s * max x 0)) ∧
        Real.exp (-(s * max x 0)) ≤ 1 := by
  constructor
  · fun_prop
  intro x
  constructor
  · exact Real.exp_pos _
  have hm : 0 ≤ max x 0 := le_max_right x 0
  have hnonneg : 0 ≤ s * max x 0 := mul_nonneg hs hm
  have hneg : -(s * max x 0) ≤ 0 := neg_nonpos.mpr hnonneg
  calc
    Real.exp (-(s * max x 0)) ≤ Real.exp 0 := Real.exp_le_exp.mpr hneg
    _ = 1 := Real.exp_zero
