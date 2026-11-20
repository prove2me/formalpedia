-- Prove2me | solution 1 for DeletionCode.CircleHash.norm_coe_eq_nearest_integer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:09.72816+00:00
-- url     : https://prove2.me/submissions/cce610c2-01c2-4c05-8957-f721e16029d5

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_DeletionCode_CircleHash

set_option autoImplicit true
open DeletionCode DeletionCode.CircleHash
open scoped BigOperators
namespace DeletionCode.CircleHash
theorem _root_.solution (r : ℝ) :
    ‖(r : UnitAddCircle)‖ = |r - (round r : ℝ)| :=
  UnitAddCircle.norm_eq
end DeletionCode.CircleHash
