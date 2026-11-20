-- Prove2me | solution 1 for DeletionCode.ExceptionalPartnerCount.fullPartners_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:57:40.119091+00:00
-- url     : https://prove2.me/submissions/001c9fb0-f0ac-4e94-bffd-437d1bb624cd

import Definitions.Def_DeletionCode_AnchorRecords
import Definitions.Def_DeletionCode_TaggedAnchorCount
import Definitions.Def_DeletionCode_ExceptionalProbability
import Definitions.Def_DeletionCode_ExceptionalCountArithmetic
import Definitions.Def_DeletionCode_ExceptionalPartnerCount
import Theorems.Thm_DeletionCode_TaggedAnchorCount_bad_record_card_le


set_option autoImplicit true
open DeletionCode DeletionCode.ExceptionalPartnerCount
open HeaderRecovery TaggedAnchorCount AlignmentTrace FiniteConflictGraph TraceEditData
open ExceptionalProbability ExceptionalCountArithmetic
open scoped BigOperators
namespace DeletionCode.ExceptionalPartnerCount
theorem _root_.solution {n : ℕ} (t k : ℕ) (x : Bits n) :
    (fullPartners t k x).card ≤
      (2 * t) * (2 * t + 2) * (2 * (4 * windowLength k)) * n ^ (2 * t - 1) * 4 ^ (2 * t) := by
  classical
  unfold fullPartners
  apply le_trans Finset.card_image_le
  have h := bad_record_card_le n (2 * t) (n - t) (4 * windowLength k)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  exact h
end DeletionCode.ExceptionalPartnerCount
