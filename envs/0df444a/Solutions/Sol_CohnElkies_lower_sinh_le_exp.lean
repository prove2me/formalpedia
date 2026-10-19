-- Prove2me | solution 1 for CohnElkies.lower_sinh_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/2a4a2052-7b38-4079-ba34-176b45261727

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
theorem _root_.solution (x : ℝ) :
    Real.sinh x ≤ Real.exp x := by
  have hpositive := Real.exp_pos (-x)
  have hpositive' := Real.exp_pos x
  rw [Real.sinh_eq]
  linarith
end CohnElkies
