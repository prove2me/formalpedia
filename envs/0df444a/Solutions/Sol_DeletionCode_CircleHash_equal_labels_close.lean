-- Prove2me | solution 1 for DeletionCode.CircleHash.equal_labels_close
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:04.878977+00:00
-- url     : https://prove2.me/submissions/680aef60-28b1-4339-bf03-def8b7960823

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_DeletionCode_CircleHash
import Theorems.Thm_DeletionCode_CircleHash_equal_labels_representatives_close

set_option autoImplicit true
open DeletionCode DeletionCode.CircleHash
open scoped BigOperators
namespace DeletionCode.CircleHash
theorem _root_.solution (Q : ℕ) (hQ : 0 < Q)
    (a b : UnitAddCircle) (hlabel : label Q a = label Q b) :
    ‖b - a‖ < 1 / (Q : ℝ) := by
  have hrep := equal_labels_representatives_close Q hQ a b hlabel
  have hquot : ‖((representative b - representative a : ℝ) : UnitAddCircle)‖ ≤
      |representative b - representative a| := by
    simpa only [Real.norm_eq_abs] using
      (QuotientAddGroup.norm_mk_le_norm
        (S := AddSubgroup.zmultiples (1 : ℝ)) (m := representative b - representative a))
  have hnorm := hquot.trans_lt hrep
  simpa only [AddCircle.coe_sub, coe_representative] using hnorm
end DeletionCode.CircleHash
