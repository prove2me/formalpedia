-- Prove2me | solution 1 for CohnElkies.lowerRiemannLog_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/eb0dc708-4a3f-48ff-a7a6-fb58ec6a9175

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
namespace CohnElkies
theorem _root_.solution (T : ℝ) :
    lowerRiemannLog T 0 = Real.log (|T| / 2) := by
  unfold lowerRiemannLog
  have hsqrt : Real.sqrt (T ^ 2 / 4) = |T| / 2 := by
    rw [show T ^ 2 / 4 = (T / 2) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_div]
    norm_num
  simp [hsqrt]
end CohnElkies
