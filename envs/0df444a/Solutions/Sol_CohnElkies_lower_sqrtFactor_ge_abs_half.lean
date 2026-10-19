-- Prove2me | solution 1 for CohnElkies.lower_sqrtFactor_ge_abs_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/18c6d7c9-f511-4bd3-9167-948d3ebda842

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution (c y : ℝ) :
    |y| / 2 ≤ Real.sqrt (c ^ 2 + (y / 2) ^ 2) := by
  apply (Real.le_sqrt (by positivity) (by positivity)).2
  nlinarith [sq_nonneg c, sq_abs y]
end CohnElkies
