-- Prove2me | solution 1 for CohnElkies.lowerRiemannLogPrimitive_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/48647f5d-114b-4ef4-b9c2-d328eded82fd

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
    {T : ℝ} (hT : T ≠ 0) (x : ℝ) :
    HasDerivAt (lowerRiemannLogPrimitive T)
      (lowerRiemannLog T x) x := by
  have hrad : 0 < x ^ 2 + T ^ 2 / 4 := by
    nlinarith [sq_nonneg x, sq_pos_of_ne_zero hT]
  have ha : 0 < |T| / 2 := half_pos (abs_pos.mpr hT)
  have hquad :
      HasDerivAt (fun u : ℝ => u ^ 2 + T ^ 2 / 4) (2 * x) x := by
    convert! ((hasDerivAt_id x).pow 2).add_const (T ^ 2 / 4)
      using 1; simp [id_eq]
  have hlog := hquad.log hrad.ne'
  have hfirst := ((hasDerivAt_id x).div_const 2).mul hlog
  have hatan := (Real.hasDerivAt_arctan (x / (|T| / 2))).comp x
    ((hasDerivAt_id x).div_const (|T| / 2))
  convert!
    (hfirst.sub (hasDerivAt_id x)).add
      (hatan.const_mul (|T| / 2)) using 1
  unfold lowerRiemannLog
  simp only [id_eq]
  rw [Real.log_sqrt hrad.le]
  have habs : |T| ^ 2 = T ^ 2 := sq_abs T
  field_simp [hrad.ne', ha.ne']
  nlinarith
end CohnElkies
