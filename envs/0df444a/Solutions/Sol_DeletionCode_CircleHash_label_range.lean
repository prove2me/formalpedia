-- Prove2me | solution 1 for DeletionCode.CircleHash.label_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:13.345455+00:00
-- url     : https://prove2.me/submissions/08f1c6e3-534b-4740-a3f2-3fd556eea5a2

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_DeletionCode_CircleHash
import Theorems.Thm_DeletionCode_CircleHash_label_nonneg
import Theorems.Thm_DeletionCode_CircleHash_label_lt

set_option autoImplicit true
open DeletionCode DeletionCode.CircleHash
open scoped BigOperators
namespace DeletionCode.CircleHash
theorem _root_.solution (Q : ℕ) (hQ : 2 ≤ Q) (z : UnitAddCircle) :
    0 ≤ label Q z ∧ label Q z < (Q : ℤ) :=
  ⟨label_nonneg Q z, label_lt Q (lt_of_lt_of_le (by decide : 0 < 2) hQ) z⟩
end DeletionCode.CircleHash
