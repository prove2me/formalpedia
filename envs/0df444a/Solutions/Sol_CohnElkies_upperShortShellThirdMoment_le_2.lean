-- Prove2me | solution 2 for CohnElkies.upperShortShellThirdMoment_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:35:17.621578+00:00
-- url     : https://prove2.me/submissions/37cccb37-6346-4cb5-847a-7355c82d1ab9

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution
    {ε δ : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Set.Icc (shortCutoff ε)
      (shortEndpoint ε), 0 ≤ shortMargin ε a) :
    upperShortShellThirdMoment ε δ ≤
      shortEndpoint ε * upperShortShellVariance ε δ := by
  have hc : 0 < shortCutoff ε := by unfold shortCutoff; positivity
  have hw1 : ContinuousOn (shortShellDensity ε) (Icc (shortCutoff ε) (shortEndpoint ε)) := by
    unfold shortShellDensity shortMargin
    refine ContinuousOn.neg (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)
    intro a ha
    have : 0 < a := lt_of_lt_of_le hc ha.1
    have := Real.cosh_pos a
    positivity
  unfold upperShortShellThirdMoment upperShortShellVariance
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on horder
  · exact ((hw1.neg.mul (continuousOn_pow 3)).mul (by fun_prop)).intervalIntegrable_of_Icc horder
  · exact (continuousOn_const.mul ((hw1.neg.mul (continuousOn_pow 2)).mul (by fun_prop))).intervalIntegrable_of_Icc horder
  · intro a ha
    have ha0 : 0 < a := lt_of_lt_of_le hc ha.1
    have hm := hmargin a ha
    have hg : 0 ≤ -shortShellDensity ε a := by
      unfold shortShellDensity; rw [neg_neg]
      exact div_nonneg (mul_nonneg hm (Real.exp_pos _).le) (by have := Real.cosh_pos a; positivity)
    have hcosh := Real.cosh_pos ((1 + δ) * a)
    calc -shortShellDensity ε a * a ^ 3 * Real.cosh ((1 + δ) * a)
        = a * (-shortShellDensity ε a * a ^ 2 * Real.cosh ((1 + δ) * a)) := by ring
      _ ≤ shortEndpoint ε * (-shortShellDensity ε a * a ^ 2 * Real.cosh ((1 + δ) * a)) :=
        mul_le_mul_of_nonneg_right ha.2 (mul_nonneg (mul_nonneg hg (sq_nonneg a)) hcosh.le)

