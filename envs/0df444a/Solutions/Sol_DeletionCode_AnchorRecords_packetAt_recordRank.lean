-- Prove2me | solution 1 for DeletionCode.AnchorRecords.packetAt_recordRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:55:59.860379+00:00
-- url     : https://prove2.me/submissions/41c9b462-c9c4-4633-b8c4-b811f8c71dbb

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceSeparation
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_AnchorRecords
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_end
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_zero
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_neg
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
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
theorem _root_.solution (trace : Trace) (c : EditColumn trace) :
    (encode trace)[recordRank trace c]? =
      some (trace.matchedAnchor c.val.val, payload (column trace c)) := by
  rw [encode_split_edit trace c]
  unfold recordRank
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp
end DeletionCode.AnchorRecords
