-- Prove2me | solution 1 for CohnElkies.lowerCoth_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/916f4b73-bb7f-4e0c-8997-25c570652191

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
    HasDerivAt lowerCoth
      (-(Real.sinh x)⁻¹ ^ 2) x := by
  have hsinh : Real.sinh x ≠ 0 :=
    (Real.sinh_pos_iff.mpr hx).ne'
  have hderiv :=
    (Real.hasDerivAt_cosh x).div
      (Real.hasDerivAt_sinh x) hsinh
  unfold lowerCoth
  convert! hderiv using 1
  rw [div_eq_mul_inv]
  have hidentity := Real.cosh_sq_sub_sinh_sq x
  field_simp [hsinh]
  nlinarith
end CohnElkies
