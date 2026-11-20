-- Prove2me | solution 1 for DeletionCode.TraceMatchedSuffix.common_suffix_of_matched_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:45:39.818302+00:00
-- url     : https://prove2.me/submissions/5071fa6f-2b11-44f0-a00c-8d8e91ddb292

import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_TraceMatchedSuffix
import Theorems.Thm_DeletionCode_TraceMatchedSuffix_matched_projections
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_end
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_zero
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_source_append
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_target_append
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_neg
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_EditAlignment_Script_trans
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
theorem _root_.solution (trace : Trace) (i m : ℕ)
    (hm : m ≤ i) (hi : i ≤ trace.length)
    (hno : ∀ j : Fin trace.length, i - m ≤ j.val → j.val < i → ¬ EditIndex trace j) :
    ∃ a b common : List Bool,
      Trace.source (trace.take i) = a ++ common ∧
      Trace.target (trace.take i) = b ++ common ∧ common.length = m := by
  let suffix : Trace := (trace.drop (i - m)).take m
  have hlength : suffix.length = m := by
    simp only [suffix, List.length_take, List.length_drop]
    omega
  have hmatched : ∀ col ∈ suffix, col.isEdit = false := by
    intro col hcol
    obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hcol
    have hjm : j < m := by omega
    have hbound : i - m + j < trace.length := by omega
    have hget' : trace.get ⟨i - m + j, hbound⟩ = col := by
      simpa only [suffix, List.get_eq_getElem, List.getElem_take, List.getElem_drop] using hget
    have hnot := hno ⟨i - m + j, hbound⟩
      (by change i - m ≤ i - m + j; omega)
      (by change i - m + j < i; omega)
    change ¬ (trace.get ⟨i - m + j, hbound⟩).isEdit = true at hnot
    rw [hget'] at hnot
    cases hbool : col.isEdit <;> simp_all
  obtain ⟨hproj, hprojlen⟩ := matched_projections suffix hmatched
  have hsplit : trace.take i = trace.take (i - m) ++ suffix := by
    dsimp [suffix]
    conv_lhs => rw [show i = (i - m) + m by omega, List.take_add]
  refine ⟨Trace.source (trace.take (i - m)), Trace.target (trace.take (i - m)), suffix.source,
    ?_, ?_, hprojlen.trans hlength⟩
  · rw [hsplit, Trace.source_append]
  · rw [hsplit, Trace.target_append, ← hproj]
end DeletionCode.TraceMatchedSuffix
