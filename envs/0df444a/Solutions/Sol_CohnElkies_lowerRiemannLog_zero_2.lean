-- Prove2me | solution 2 for CohnElkies.lowerRiemannLog_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:56:13.741192+00:00
-- url     : https://prove2.me/submissions/818e5799-4739-4b6a-9a7e-2c3e6bda6f3b

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


theorem solution (T : ℝ) :
    lowerRiemannLog T 0 = Real.log (|T| / 2) := by
  unfold lowerRiemannLog
  rw [show (0:ℝ)^2 + T^2/4 = (|T|/2)^2 by rw [div_pow, sq_abs]; ring, Real.sqrt_sq (by positivity)]

