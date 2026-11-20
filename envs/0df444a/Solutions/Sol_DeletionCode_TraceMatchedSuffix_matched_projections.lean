-- Prove2me | solution 1 for DeletionCode.TraceMatchedSuffix.matched_projections
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:41:43.782954+00:00
-- url     : https://prove2.me/submissions/bb21fe11-ded6-4022-b035-c2acc44803d2

import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_TraceMatchedSuffix
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
open DeletionCode DeletionCode.TraceMatchedSuffix
open AlignmentTrace FiniteConflictGraph TraceSeparation
namespace DeletionCode.TraceMatchedSuffix
theorem _root_.solution (trace : Trace)
    (hmatched : ∀ col ∈ trace, col.isEdit = false) :
    trace.source = trace.target ∧ trace.source.length = trace.length := by
  induction trace with
  | nil => exact ⟨rfl, rfl⟩
  | cons col rest ih =>
    have hcol := hmatched col (List.mem_cons_self)
    have hrest : ∀ c ∈ rest, c.isEdit = false := by
      intro c hc
      exact hmatched c (List.mem_cons_of_mem col hc)
    have h := ih hrest
    cases col with
    | matched bit =>
      simp only [Trace.source, Trace.target, List.length_cons]
      exact ⟨congrArg (List.cons bit) h.1, congrArg (fun n => n + 1) h.2⟩
    | deletion bit => simp only [Column.isEdit, Bool.true_eq_false] at hcol
    | insertion bit => simp only [Column.isEdit, Bool.true_eq_false] at hcol
end DeletionCode.TraceMatchedSuffix
