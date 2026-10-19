-- Prove2me | solution 1 for CohnElkies.saddleGaussianTailSet_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/0173f0f0-4089-4e21-9509-9841b8a1021c

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace CohnElkies
theorem _root_.solution (R : ℝ) :
    MeasurableSet (saddleGaussianTailSet R) := by
  unfold saddleGaussianTailSet
  exact measurableSet_le measurable_const measurable_abs
end CohnElkies
