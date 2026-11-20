-- Prove2me | solution 1 for DeletionCode.ExceptionalPartnerCount.shortPartners_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:56:57.688479+00:00
-- url     : https://prove2.me/submissions/e50fcae3-da54-4db9-9863-dbe9d450ff5d

import Definitions.Def_DeletionCode_AnchorRecords
import Definitions.Def_DeletionCode_TaggedAnchorCount
import Definitions.Def_DeletionCode_ExceptionalProbability
import Definitions.Def_DeletionCode_ExceptionalCountArithmetic
import Definitions.Def_DeletionCode_ExceptionalPartnerCount
import Theorems.Thm_DeletionCode_TaggedAnchorCount_record_card


set_option autoImplicit true
open DeletionCode DeletionCode.ExceptionalPartnerCount
open HeaderRecovery TaggedAnchorCount AlignmentTrace FiniteConflictGraph TraceEditData
open ExceptionalProbability ExceptionalCountArithmetic
open scoped BigOperators
namespace DeletionCode.ExceptionalPartnerCount
theorem _root_.solution {n : ℕ} (t : ℕ) (x : Bits n) :
    (shortPartners t x).card ≤ ∑ d ∈ Finset.range t, n ^ (2 * d) * 4 ^ (2 * d) := by
  classical
  unfold shortPartners
  apply le_trans Finset.card_biUnion_le
  apply Finset.sum_le_sum
  intro d _
  calc
    _ ≤ (Finset.univ : Finset (Record n (2 * d))).card := Finset.card_image_le
    _ = _ := by rw [Finset.card_univ, record_card]
end DeletionCode.ExceptionalPartnerCount
