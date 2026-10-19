-- Prove2me | solution 2 for CohnElkies.upperShortShellVariance_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:11:08.733655+00:00
-- url     : https://prove2.me/submissions/c39f6822-eb2e-4c14-969e-ddabf547671a

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
    0 ≤ upperShortShellVariance ε δ := by
  unfold upperShortShellVariance
  apply intervalIntegral.integral_nonneg horder
  intro a ha
  have h0 : 0 < shortCutoff ε := by unfold shortCutoff; positivity
  have ha0 : 0 < a := lt_of_lt_of_le h0 ha.1
  have hm := hmargin a ha
  unfold shortShellDensity
  rw [neg_neg]
  have := Real.cosh_pos a
  exact mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg hm (Real.exp_pos _).le) (by positivity)) (sq_nonneg a)) (Real.cosh_pos _).le

