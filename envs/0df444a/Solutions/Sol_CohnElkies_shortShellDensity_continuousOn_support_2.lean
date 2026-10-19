-- Prove2me | solution 2 for CohnElkies.shortShellDensity_continuousOn_support
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:07:55.83718+00:00
-- url     : https://prove2.me/submissions/9d00daf7-eac3-4523-9ee9-9f346028e6ac

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
    {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (shortShellDensity ε)
      (Icc (shortCutoff ε) (shortEndpoint ε)) := by
  unfold shortShellDensity shortMargin
  apply ContinuousOn.neg
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro a ha
  have h0 : 0 < shortCutoff ε := by unfold shortCutoff; positivity
  have ha0 : 0 < a := lt_of_lt_of_le h0 ha.1
  have := Real.cosh_pos a
  positivity

