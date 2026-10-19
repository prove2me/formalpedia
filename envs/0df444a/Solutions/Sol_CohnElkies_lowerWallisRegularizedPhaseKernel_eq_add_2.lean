-- Prove2me | solution 2 for CohnElkies.lowerWallisRegularizedPhaseKernel_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:05:42.748848+00:00
-- url     : https://prove2.me/submissions/ca19b3a1-2d76-42bc-ad6d-9ea4a615c8a7

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology


theorem solution
    (a u t : ℝ) :
    lowerWallisRegularizedPhaseKernel a u t =
      lowerWallisPhaseKernel u t +
        ((1 - Real.exp (-t)) *
          (Real.exp (-a * t) - 1) * Real.cos (u * t)) /
            t ^ 2 := by
  unfold lowerWallisRegularizedPhaseKernel lowerWallisPhaseKernel
  ring

