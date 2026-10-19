-- Prove2me | solution 1 for CohnElkies.saddle_log_sq_le_four_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/69e96bed-07ef-41f9-8a85-a7948c2fb75a

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x) ^ 2 ≤ 4 * x := by
  have hxpos : 0 < x := by linarith
  have hspos : 0 < Real.sqrt x :=
    Real.sqrt_pos.2 hxpos
  have hsquare := Real.sq_sqrt hxpos.le
  have hlogsplit :
      Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [← hsquare, Real.log_pow]
    norm_num
  have hslog := Real.log_le_sub_one_of_pos hspos
  have hlognonnegative : 0 ≤ Real.log x :=
    Real.log_nonneg hx
  have hupper : Real.log x ≤ 2 * Real.sqrt x := by
    rw [hlogsplit]
    nlinarith
  have hfactor := mul_nonneg
    (sub_nonneg.mpr hupper)
    (add_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (Real.sqrt_nonneg x))
      hlognonnegative)
  nlinarith
end CohnElkies
