-- Prove2me | solution 1 for CohnElkies.saddle_integral_exp_neg_mul_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/6378f43d-5616-4d71-91f4-0334fc9e3a60

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {a : ℝ} (ha : 0 < a) :
    (∫ T : ℝ, Real.exp (-a * |T|)) = 2 / a := by
  have hhalf := integral_exp_mul_Ioi
    (neg_lt_zero.mpr ha) (0 : ℝ)
  calc
    (∫ T : ℝ, Real.exp (-a * |T|)) =
        2 * ∫ T : ℝ in Ioi (0 : ℝ),
          Real.exp (-a * T) :=
      (integral_comp_abs
        (f := fun T : ℝ => Real.exp (-a * T)))
    _ = 2 / a := by
      rw [hhalf]
      simp [div_eq_mul_inv]
end CohnElkies
