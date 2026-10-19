-- Prove2me | solution 2 for CohnElkies.lowerCoth_pos
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:59:19.861143+00:00
-- url     : https://prove2.me/submissions/978cc728-75fa-4813-9fe7-6d832bbe5508

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


theorem solution {x : ℝ} (hx : 0 < x) :
    0 < lowerCoth x := by
  unfold lowerCoth
  exact div_pos (Real.cosh_pos x) (Real.sinh_pos_iff.mpr hx)

