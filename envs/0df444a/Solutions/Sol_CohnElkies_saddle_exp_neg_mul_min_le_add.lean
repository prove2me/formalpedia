-- Prove2me | solution 1 for CohnElkies.saddle_exp_neg_mul_min_le_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/6d3f6154-73cd-43e1-9abf-268ef441f0b1

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
    {a x y : ℝ} (ha : 0 ≤ a) :
    Real.exp (-a * min x y) ≤
      Real.exp (-a * x) + Real.exp (-a * y) := by
  have hmax :
      Real.exp (-a * min x y) =
        max (Real.exp (-a * x)) (Real.exp (-a * y)) := by
    rcases le_total x y with hxy | hyx
    · rw [min_eq_left hxy, max_eq_left]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hxy)]
    · rw [min_eq_right hyx, max_eq_right]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hyx)]
  rw [hmax]
  exact max_le_add_of_nonneg
    (Real.exp_pos (-a * x)).le (Real.exp_pos (-a * y)).le
end CohnElkies
