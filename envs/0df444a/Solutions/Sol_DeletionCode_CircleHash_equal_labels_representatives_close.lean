-- Prove2me | solution 1 for DeletionCode.CircleHash.equal_labels_representatives_close
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:48.210169+00:00
-- url     : https://prove2.me/submissions/fe3632e6-7df5-41c7-be03-560c7a0dc7d5

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_DeletionCode_CircleHash
import Theorems.Thm_DeletionCode_CircleHash_equal_scaled_floors_close

set_option autoImplicit true
open DeletionCode DeletionCode.CircleHash
open scoped BigOperators
namespace DeletionCode.CircleHash
theorem _root_.solution (Q : ℕ) (hQ : 0 < Q)
    (a b : UnitAddCircle) (hlabel : label Q a = label Q b) :
    |representative b - representative a| < 1 / (Q : ℝ) :=
  equal_scaled_floors_close Q hQ (representative a) (representative b) hlabel
end DeletionCode.CircleHash
