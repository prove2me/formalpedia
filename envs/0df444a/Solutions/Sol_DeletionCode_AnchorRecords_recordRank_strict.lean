-- Prove2me | solution 1 for DeletionCode.AnchorRecords.recordRank_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:59:38.532877+00:00
-- url     : https://prove2.me/submissions/09866d1f-ba4c-4b93-b9a7-e0ba6fe112b6

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceSeparation
import Mathlib.Data.List.OfFn
import Definitions.Def_DeletionCode_AnchorRecords
import Theorems.Thm_DeletionCode_AnchorRecords_encode_length
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_deletions_append
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_insertions_append
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
import Theorems.Thm_DeletionCode_TraceSeparation_deletions_take_mono
import Theorems.Thm_DeletionCode_TraceSeparation_insertions_take_mono
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
theorem _root_.solution (trace : Trace) (c d : EditColumn trace)
    (hcd : c.val.val < d.val.val) : recordRank trace c < recordRank trace d := by
  have hdel := TraceSeparation.deletions_take_mono trace
    (show c.val.val + 1 ≤ d.val.val by omega)
  have hins := TraceSeparation.insertions_take_mono trace
    (show c.val.val + 1 ≤ d.val.val by omega)
  have hstep : Trace.deletions (trace.take (c.val.val + 1)) +
      Trace.insertions (trace.take (c.val.val + 1)) =
        Trace.deletions (trace.take c.val.val) + Trace.insertions (trace.take c.val.val) + 1 := by
    rw [List.take_succ_eq_append_getElem c.val.isLt,
      Trace.deletions_append, Trace.insertions_append]
    change Trace.deletions (trace.take c.val.val) + Trace.deletions [column trace c] +
      (Trace.insertions (trace.take c.val.val) + Trace.insertions [column trace c]) = _
    rcases column_cases trace c with ⟨bit, hc⟩ | ⟨bit, hc⟩
    · simp only [hc, Trace.deletions, Trace.insertions] <;> omega
    · simp only [hc, Trace.deletions, Trace.insertions] <;> omega
  simp only [recordRank, encode_length]
  omega
end DeletionCode.AnchorRecords
