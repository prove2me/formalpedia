-- Prove2me | solution 1 for CohnElkies.lowerCoth_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/1aa29e7e-c769-43f9-9e73-5ce75a5e28df

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
theorem _root_.solution {x : ℝ} (hx : 0 < x) :
    0 < lowerCoth x := by
  unfold lowerCoth
  exact div_pos (Real.cosh_pos x) (Real.sinh_pos_iff.mpr hx)
end CohnElkies
