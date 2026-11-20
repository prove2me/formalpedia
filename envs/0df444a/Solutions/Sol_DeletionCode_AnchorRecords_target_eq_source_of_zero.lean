-- Prove2me | solution 1 for DeletionCode.AnchorRecords.target_eq_source_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:01:34.350847+00:00
-- url     : https://prove2.me/submissions/ca88cdab-2712-4a6a-b9b0-445ea510cdbb

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceSeparation
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_AnchorRecords
import Theorems.Thm_DeletionCode_AnchorRecords_encode_length
import Theorems.Thm_DeletionCode_AnchorRecords_decode_encode
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_end
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_zero
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_neg
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm
import Theorems.Thm_DeletionCode_FiniteRelationBlocks_mem_selectedBlocks
import Theorems.Thm_DeletionCode_FiniteWalkRules_rational_step
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_empty
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_insert
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
attribute [local simp] DeletionCode.AlignmentTrace.Trace.matchedAnchor_end
attribute [local simp] DeletionCode.AlignmentTrace.Trace.matchedAnchor_zero
attribute [local simp] DeletionCode.BlockPartition.mem_attachedBlocks
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blocks
attribute [local simp] DeletionCode.CatalogueAlgebra.rational_neg
attribute [local simp] DeletionCode.CatalogueAlgebra.rational_zero
attribute [local simp] DeletionCode.ComponentFibers.mem_fiber
attribute [local simp] DeletionCode.FiniteRelationBlocks.mem_selectedBlocks
attribute [local simp] DeletionCode.FiniteWalkRules.rational_step
attribute [local simp] DeletionCode.FiniteWalkRules.selectedRules_empty
attribute [local simp] DeletionCode.FiniteWalkRules.selectedRules_insert
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk



set_option autoImplicit true
open DeletionCode DeletionCode.AnchorRecords
open AlignmentTrace TraceEditData
namespace DeletionCode.AnchorRecords
theorem _root_.solution (trace : Trace)
    (hdel : trace.deletions = 0) (hins : trace.insertions = 0) :
    trace.target = trace.source := by
  have hlen : (encode trace).length = 0 := by rw [encode_length, hdel, hins]
  have he : encode trace = [] := List.length_eq_zero_iff.mp hlen
  simpa only [he, decode, decodeFrom] using (decode_encode trace).symm
end DeletionCode.AnchorRecords
