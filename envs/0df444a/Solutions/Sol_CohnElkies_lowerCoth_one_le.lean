-- Prove2me | solution 1 for CohnElkies.lowerCoth_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/36c11dfa-d735-483c-b194-dbb908a34aaf

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
    1 ≤ lowerCoth x := by
  have hsinh : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  unfold lowerCoth
  apply (le_div_iff₀ hsinh).2
  rw [one_mul, Real.sinh_eq, Real.cosh_eq]
  linarith [Real.exp_pos (-x)]
end CohnElkies
