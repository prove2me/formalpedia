-- Prove2me | solution 1 for DeletionCode.TraceSpectrumAssembly.hybrid_increment_of_not_edit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:53:13.437528+00:00
-- url     : https://prove2.me/submissions/b1442d57-d797-4c59-837f-07b2f6597460

import Definitions.Def_DeletionCode_TraceEditData
import Definitions.Def_DeletionCode_TraceMatchedSuffix
import Definitions.Def_DeletionCode_SpectrumPrefixChange
import Definitions.Def_DeletionCode_TraceSpectrumAssembly
import Theorems.Thm_DeletionCode_TraceSpectrumAssembly_hybrid_before
import Theorems.Thm_DeletionCode_TraceSpectrumAssembly_hybrid_after
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
open DeletionCode DeletionCode.TraceSpectrumAssembly
open AlignmentTrace FiniteConflictGraph TraceEditData SignedSupport
open SpectrumPrefixChange TraceMatchedSuffix
open scoped BigOperators
namespace DeletionCode.TraceSpectrumAssembly
theorem _root_.solution (trace : Trace) (i : Fin trace.length)
    (hnot : ¬ EditIndex trace i) (L : ℕ) (g : Gram L) :
    spectrum (hybrid trace (i.val + 1)) L g - spectrum (hybrid trace i.val) L g = 0 := by
  cases hc : trace.get i with
  | matched bit =>
    rw [hybrid_after, hybrid_before, hc]
    simp only [Trace.source, Trace.target, List.append_assoc, List.singleton_append, sub_self]
  | deletion bit =>
    exact False.elim (hnot (by simp only [EditIndex, hc, Column.isEdit]))
  | insertion bit =>
    exact False.elim (hnot (by simp only [EditIndex, hc, Column.isEdit]))
end DeletionCode.TraceSpectrumAssembly
