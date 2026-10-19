-- Prove2me | solution 2 for CohnElkies.lowerGammaScaledCappedClipped_eq_lowerClip_add
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:01:51.596983+00:00
-- url     : https://prove2.me/submissions/ac34ab91-3abf-4a3b-a445-a1efef82fea8

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology


theorem solution
    (d : ℕ) (c D n Y : ℝ) :
    lowerGammaScaledCappedClipped d c D n Y =
      lowerGammaScaledCappedLowerClip d c D n Y + n := by
  unfold lowerGammaScaledCappedClipped lowerGammaScaledCappedLowerClip
  rw [← max_add_add_right, neg_add_cancel]

