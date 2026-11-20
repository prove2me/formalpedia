-- Prove2me | solution 1 for DeletionCode.CircleHash.equal_labels_small_representative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:07.802728+00:00
-- url     : https://prove2.me/submissions/d94bdbb3-6555-4234-b0b2-1aa8694be272

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
    ∃ r : ℝ, (r : UnitAddCircle) = b - a ∧
      -(1 / (Q : ℝ)) < r ∧ r < 1 / (Q : ℝ) := by
  refine ⟨representative b - representative a, ?_, ?_⟩
  · simp only [AddCircle.coe_sub, coe_representative]
  · exact abs_lt.mp (equal_labels_representatives_close Q hQ a b hlabel)
end DeletionCode.CircleHash
