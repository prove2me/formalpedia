-- Prove2me | solution 2 for CohnElkies.upperPositiveShellVariance_pos
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:05:48.375385+00:00
-- url     : https://prove2.me/submissions/ce7c11d0-8637-4585-aed9-5c1ccd8fc8f9

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
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) :
    0 < upperPositiveShellVariance ε δ := by
  unfold upperPositiveShellVariance
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · apply Continuous.intervalIntegrable
    unfold positiveShellDensity
    have : ∀ a, Real.cosh a ≠ 0 := fun a => (Real.cosh_pos a).ne'
    fun_prop (disch := exact this _)
  · intro a ha
    have hl : 0 < shellLocation ε := by unfold shellLocation; positivity
    have ha0 : 0 < a := by linarith [ha.1]
    unfold positiveShellDensity shellWeight
    have := Real.cosh_pos a
    have := Real.cosh_pos ((1 + δ) * a)
    positivity
  · linarith

