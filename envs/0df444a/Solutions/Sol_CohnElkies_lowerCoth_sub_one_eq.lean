-- Prove2me | solution 1 for CohnElkies.lowerCoth_sub_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/bbd0f1e6-c9a6-4456-8174-25d27faa8169

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
theorem _root_.solution
    {x : ℝ} (hx : 0 < x) :
    lowerCoth x - 1 = Real.exp (-x) / Real.sinh x := by
  have hsinh : Real.sinh x ≠ 0 :=
    (Real.sinh_pos_iff.mpr hx).ne'
  unfold lowerCoth
  field_simp [hsinh]
  rw [Real.cosh_eq, Real.sinh_eq]
  ring
end CohnElkies
