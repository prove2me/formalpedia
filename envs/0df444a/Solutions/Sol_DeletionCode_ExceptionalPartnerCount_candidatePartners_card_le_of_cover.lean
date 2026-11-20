-- Prove2me | solution 1 for DeletionCode.ExceptionalPartnerCount.candidatePartners_card_le_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:59:45.466308+00:00
-- url     : https://prove2.me/submissions/18347dc4-b784-418c-a51c-491d2ed75456

import Definitions.Def_DeletionCode_AnchorRecords
import Definitions.Def_DeletionCode_TaggedAnchorCount
import Definitions.Def_DeletionCode_ExceptionalProbability
import Definitions.Def_DeletionCode_ExceptionalCountArithmetic
import Definitions.Def_DeletionCode_ExceptionalPartnerCount
import Theorems.Thm_DeletionCode_ExceptionalPartnerCount_shortPartners_card_le
import Theorems.Thm_DeletionCode_ExceptionalPartnerCount_fullPartners_card_le
import Theorems.Thm_DeletionCode_ExceptionalCountArithmetic_combined_records_bound


set_option autoImplicit true
open DeletionCode DeletionCode.ExceptionalPartnerCount
open HeaderRecovery TaggedAnchorCount AlignmentTrace FiniteConflictGraph TraceEditData
open ExceptionalProbability ExceptionalCountArithmetic
open scoped BigOperators
namespace DeletionCode.ExceptionalPartnerCount
theorem _root_.solution {n : ℕ} (t k : ℕ) (x : Bits n)
    (hn : 1 ≤ n)
    (hcover : candidatePartners t k x ⊆ shortPartners t x ∪ fullPartners t k x) :
    (candidatePartners t k x).card ≤ exceptionalConstant t * windowLength k * n ^ (2 * t - 1) := by
  calc
    _ ≤ (shortPartners t x ∪ fullPartners t k x).card := Finset.card_le_card hcover
    _ ≤ (shortPartners t x).card + (fullPartners t k x).card := Finset.card_union_le _ _
    _ ≤ (∑ d ∈ Finset.range t, n ^ (2 * d) * 4 ^ (2 * d)) +
        (2 * t) * (2 * t + 2) * (2 * (4 * windowLength k)) * n ^ (2 * t - 1) * 4 ^ (2 * t) :=
      Nat.add_le_add (shortPartners_card_le t x) (fullPartners_card_le t k x)
    _ ≤ _ := combined_records_bound n t (windowLength k) hn (by unfold windowLength; omega)
end DeletionCode.ExceptionalPartnerCount
