-- Prove2me | solution 1 for DeletionCode.CircleHash.equal_hash_labels_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:19:17.674547+00:00
-- url     : https://prove2.me/submissions/548c67bb-1720-4708-a37a-6f090110488b

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_DeletionCode_CircleHash
import Theorems.Thm_DeletionCode_CircleHash_equal_labels_close

set_option autoImplicit true
open DeletionCode DeletionCode.CircleHash
open scoped BigOperators
namespace DeletionCode.CircleHash
theorem _root_.solution {V : Type*} [AddCommGroup V]
    (H : V →+ UnitAddCircle) (Q : ℕ) (hQ : 2 ≤ Q) (p p' : V)
    (hlabel : label Q (H p) = label Q (H p')) :
    ‖H (p' - p)‖ < 1 / (Q : ℝ) := by
  rw [map_sub]
  exact equal_labels_close Q (lt_of_lt_of_le (by decide : 0 < 2) hQ) (H p) (H p') hlabel
end DeletionCode.CircleHash
