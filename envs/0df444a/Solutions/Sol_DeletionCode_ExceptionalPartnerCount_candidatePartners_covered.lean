-- Prove2me | solution 1 for DeletionCode.ExceptionalPartnerCount.candidatePartners_covered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:10:46.706999+00:00
-- url     : https://prove2.me/submissions/54f82420-1b55-45bb-a4d8-b332f5411c55

import Definitions.Def_DeletionCode_AnchorRecords
import Definitions.Def_DeletionCode_TaggedAnchorCount
import Definitions.Def_DeletionCode_ExceptionalProbability
import Definitions.Def_DeletionCode_ExceptionalCountArithmetic
import Definitions.Def_DeletionCode_ExceptionalPartnerCount
import Theorems.Thm_DeletionCode_ExceptionalPartnerCount_decodeWord_eq
import Theorems.Thm_DeletionCode_ExceptionalPartnerCount_bad_record_of_not_separated
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_source_length
import Theorems.Thm_DeletionCode_AnchorRecords_decode_encode
import Theorems.Thm_DeletionCode_AnchorRecords_exists_finite_record
import Theorems.Thm_DeletionCode_AnchorRecords_target_eq_source_of_zero
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm
import Theorems.Thm_DeletionCode_EditAlignment_Script_trans
import Theorems.Thm_DeletionCode_ExceptionalProbability_mem_candidatePartners
attribute [local simp] DeletionCode.ExceptionalProbability.mem_candidatePartners



set_option autoImplicit true
open DeletionCode DeletionCode.ExceptionalPartnerCount
open HeaderRecovery TaggedAnchorCount AlignmentTrace FiniteConflictGraph TraceEditData
open ExceptionalProbability ExceptionalCountArithmetic
open scoped BigOperators
namespace DeletionCode.ExceptionalPartnerCount
theorem _root_.solution {n : ℕ} (t k : ℕ) (x : Bits n) :
    candidatePartners t k x ⊆ shortPartners t x ∪ fullPartners t k x := by
  classical
  intro y hy
  obtain ⟨hxy, d, trace, hs, ht, hd, hi, hcase⟩ :=
    (mem_candidatePartners t k x y).mp hy
  have hdpos : 1 ≤ d := by
    by_contra h
    have hzero : d = 0 := by omega
    have hz := AnchorRecords.target_eq_source_of_zero trace (hd.trans hzero) (hi.trans hzero)
    rw [hs, ht] at hz
    exact hxy (List.ofFn_injective hz).symm
  have hlen : trace.source.length = n := by rw [hs, List.length_ofFn]
  obtain ⟨anchors, data, hrecord⟩ := AnchorRecords.exists_finite_record trace n d hlen hd hi hdpos
  let record : Record n (2 * d) := (anchors, data)
  have hp : packets record = AnchorRecords.encode trace := hrecord
  have hdecode : decodeWord x record = y := by
    apply decodeWord_eq
    rw [hp, ← hs, AnchorRecords.decode_encode, ht]
  rcases hcase with hshort | ⟨hfull, hnot⟩
  · apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    exact ⟨d, Finset.mem_range.mpr hshort, Finset.mem_image.mpr ⟨record, Finset.mem_univ _, hdecode⟩⟩
  · subst t
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨record, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hdecode⟩
    have hm : trace.matchedCount = n - d := by
      have h := trace.source_length
      omega
    rw [← hm]
    exact bad_record_of_not_separated trace record hp hnot
end DeletionCode.ExceptionalPartnerCount
