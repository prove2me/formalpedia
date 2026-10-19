-- Prove2me | solution 2 for CohnElkies.saddleGaussianTailSet_measurable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:56:22.186674+00:00
-- url     : https://prove2.me/submissions/0d092f0b-68e5-43df-8b6b-1823c53f60ab

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


theorem solution (R : ℝ) :
    MeasurableSet (saddleGaussianTailSet R) := by
  exact measurableSet_le measurable_const continuous_abs.measurable

