-- Prove2me | solution 1 for CohnElkies.lowerCoth_log_le_four_exp_neg_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/99b1cc28-1096-4052-82db-0c66c6996fb9

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerCoth_pos
import Theorems.Thm_CohnElkies_lowerCoth_sub_one_eq
import Theorems.Thm_CohnElkies_lower_sinh_ge_exp_quarter

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
    {x : ℝ} (hx : 1 ≤ x) :
    Real.log (lowerCoth x) ≤
      4 * Real.exp (-2 * x) := by
  have hxpos : 0 < x := by linarith
  have hsinh : 0 < Real.sinh x :=
    Real.sinh_pos_iff.mpr hxpos
  calc
    Real.log (lowerCoth x) ≤ lowerCoth x - 1 :=
      Real.log_le_sub_one_of_pos (lowerCoth_pos hxpos)
    _ = Real.exp (-x) / Real.sinh x :=
      lowerCoth_sub_one_eq hxpos
    _ ≤ Real.exp (-x) / (Real.exp x / 4) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le
        (by positivity) (lower_sinh_ge_exp_quarter hx)
    _ = 4 * Real.exp (-2 * x) := by
      rw [show -2 * x = -x - x by ring,
        Real.exp_sub]
      field_simp [Real.exp_ne_zero x]
end CohnElkies
