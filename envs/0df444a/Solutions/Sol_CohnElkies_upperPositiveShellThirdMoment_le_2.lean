-- Prove2me | solution 2 for CohnElkies.upperPositiveShellThirdMoment_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:15:03.974915+00:00
-- url     : https://prove2.me/submissions/0f48eebb-6399-4658-a4a5-625c94abcb60

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
    {ε δ : ℝ} (hε : 0 < ε) :
    upperPositiveShellThirdMoment ε δ ≤
      (shellLocation ε + 1) *
        upperPositiveShellVariance ε δ := by
  unfold upperPositiveShellThirdMoment upperPositiveShellVariance
  have hl : 0 < shellLocation ε := by unfold shellLocation; positivity
  have hc : Continuous (positiveShellDensity ε) := by
    unfold positiveShellDensity
    exact continuous_const.div Real.continuous_cosh (fun a => (Real.cosh_pos a).ne')
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by linarith)
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  · intro a ha
    have ha0 : 0 ≤ a := by linarith [ha.1]
    have hp : 0 ≤ positiveShellDensity ε a * Real.cosh ((1 + δ) * a) := by
      unfold positiveShellDensity shellWeight
      have := Real.cosh_pos a; have := Real.cosh_pos ((1 + δ) * a); positivity
    have : a ^ 3 ≤ (shellLocation ε + 1) * a ^ 2 := by nlinarith [ha.2, sq_nonneg a]
    nlinarith [mul_le_mul_of_nonneg_left this hp]

