-- Prove2me | solution 1 for DeletionCode.CircleHash.norm_coe_le_integer_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:08.318364+00:00
-- url     : https://prove2.me/submissions/efe70895-5cfe-4976-81e2-ce816113e531

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_DeletionCode_CircleHash
import Theorems.Thm_DeletionCode_CircleHash_norm_coe_eq_nearest_integer

set_option autoImplicit true
open DeletionCode DeletionCode.CircleHash
open scoped BigOperators
namespace DeletionCode.CircleHash
theorem _root_.solution (r : ℝ) (z : ℤ) :
    ‖(r : UnitAddCircle)‖ ≤ |r - (z : ℝ)| := by
  rw [norm_coe_eq_nearest_integer]
  exact round_le r z
end DeletionCode.CircleHash
