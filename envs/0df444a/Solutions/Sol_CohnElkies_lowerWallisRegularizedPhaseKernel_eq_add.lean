-- Prove2me | solution 1 for CohnElkies.lowerWallisRegularizedPhaseKernel_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/eda27c03-f937-4947-a433-f2976e053fa3

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
namespace CohnElkies
theorem _root_.solution
    (a u t : ℝ) :
    lowerWallisRegularizedPhaseKernel a u t =
      lowerWallisPhaseKernel u t +
        ((1 - Real.exp (-t)) *
          (Real.exp (-a * t) - 1) * Real.cos (u * t)) /
            t ^ 2 := by
  unfold lowerWallisRegularizedPhaseKernel lowerWallisPhaseKernel
  ring
end CohnElkies
