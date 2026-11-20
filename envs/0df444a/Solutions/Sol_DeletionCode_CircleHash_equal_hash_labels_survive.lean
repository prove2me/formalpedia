-- Prove2me | solution 1 for DeletionCode.CircleHash.equal_hash_labels_survive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:19.317175+00:00
-- url     : https://prove2.me/submissions/3b1227c5-79ae-4c89-894a-080793617682

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_DeletionCode_CircleHash
import Theorems.Thm_DeletionCode_CircleHash_equal_hash_labels_norm_lt

set_option autoImplicit true
open DeletionCode DeletionCode.CircleHash
open scoped BigOperators
namespace DeletionCode.CircleHash
theorem _root_.solution {V : Type*} [AddCommGroup V]
    (H : V →+ UnitAddCircle) (Q : ℕ) (hQ : 2 ≤ Q) (p p' : V)
    {K₀ : Set V} (hlabel : label Q (H p) = label Q (H p'))
    (hcat : p' - p ∈ K₀) : p' - p ∈ surviving H Q K₀ :=
  ⟨hcat, equal_hash_labels_norm_lt H Q hQ p p' hlabel⟩
end DeletionCode.CircleHash
