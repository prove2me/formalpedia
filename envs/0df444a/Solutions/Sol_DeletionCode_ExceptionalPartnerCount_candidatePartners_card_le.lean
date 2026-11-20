-- Prove2me | solution 1 for DeletionCode.ExceptionalPartnerCount.candidatePartners_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:14:16.720831+00:00
-- url     : https://prove2.me/submissions/2e26d776-35b7-48fe-b9bc-b095c19a4068

import Definitions.Def_DeletionCode_AnchorRecords
import Definitions.Def_DeletionCode_TaggedAnchorCount
import Definitions.Def_DeletionCode_ExceptionalProbability
import Definitions.Def_DeletionCode_ExceptionalCountArithmetic
import Definitions.Def_DeletionCode_ExceptionalPartnerCount
import Theorems.Thm_DeletionCode_ExceptionalPartnerCount_candidatePartners_card_le_of_cover
import Theorems.Thm_DeletionCode_ExceptionalPartnerCount_candidatePartners_covered

set_option autoImplicit true
open DeletionCode DeletionCode.ExceptionalPartnerCount
open HeaderRecovery TaggedAnchorCount AlignmentTrace FiniteConflictGraph TraceEditData
open ExceptionalProbability ExceptionalCountArithmetic
open scoped BigOperators
namespace DeletionCode.ExceptionalPartnerCount
theorem _root_.solution {n : ℕ} (t k : ℕ) (x : Bits n) (hn : 1 ≤ n) :
    (candidatePartners t k x).card ≤ exceptionalConstant t * windowLength k * n ^ (2 * t - 1) :=
  candidatePartners_card_le_of_cover t k x hn (candidatePartners_covered t k x)
end DeletionCode.ExceptionalPartnerCount
