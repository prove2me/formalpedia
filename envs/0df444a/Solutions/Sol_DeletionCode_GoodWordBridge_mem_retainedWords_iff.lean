-- Prove2me | solution 1 for DeletionCode.GoodWordBridge.mem_retainedWords_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:02:37.914722+00:00
-- url     : https://prove2.me/submissions/b83a0009-f00f-4b33-98a7-be6d6111ca0b

import Definitions.Def_DeletionCode_CodeSelection
import Definitions.Def_DeletionCode_UniqueWordCount
import Definitions.Def_DeletionCode_ExceptionalProbability
import Definitions.Def_DeletionCode_ObstructionProbability
import Definitions.Def_DeletionCode_GoodWordBridge
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_end
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_zero
import Theorems.Thm_DeletionCode_BipartiteSelection_mem_goodVertices
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_neg
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm
import Theorems.Thm_DeletionCode_EditAlignment_Script_trans
import Theorems.Thm_DeletionCode_ExceptionalProbability_mem_candidatePartners
import Theorems.Thm_DeletionCode_FiniteRelationBlocks_mem_selectedBlocks
import Theorems.Thm_DeletionCode_FiniteWalkRules_rational_step
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_empty
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_insert
import Theorems.Thm_DeletionCode_IntegerTorusMap_jointHash_apply
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
import Theorems.Thm_DeletionCode_UniqueWordCount_mem_uniqueWords
attribute [local simp] DeletionCode.AlignmentTrace.Trace.matchedAnchor_end
attribute [local simp] DeletionCode.AlignmentTrace.Trace.matchedAnchor_zero
attribute [local simp] DeletionCode.BipartiteSelection.mem_goodVertices
attribute [local simp] DeletionCode.BlockPartition.mem_attachedBlocks
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blocks
attribute [local simp] DeletionCode.CatalogueAlgebra.rational_neg
attribute [local simp] DeletionCode.CatalogueAlgebra.rational_zero
attribute [local simp] DeletionCode.ComponentFibers.mem_fiber
attribute [local simp] DeletionCode.ExceptionalProbability.mem_candidatePartners
attribute [local simp] DeletionCode.FiniteRelationBlocks.mem_selectedBlocks
attribute [local simp] DeletionCode.FiniteWalkRules.rational_step
attribute [local simp] DeletionCode.FiniteWalkRules.selectedRules_empty
attribute [local simp] DeletionCode.FiniteWalkRules.selectedRules_insert
attribute [local simp] DeletionCode.IntegerTorusMap.jointHash_apply
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk



set_option autoImplicit true
open DeletionCode DeletionCode.GoodWordBridge
open Windows HeaderRecovery SignedSupport CircleHash ConflictGraphWitness
open ExceptionalProbability ObstructionProbability BipartiteSelection
variable {n : ℕ}
namespace DeletionCode.GoodWordBridge
theorem _root_.solution (t k Q : ℕ) (weights : Gram (windowLength k) → ℝ)
    (x : Bits n) :
    x ∈ retainedWords t k Q weights ↔
      ∃ v : Vertex (n := n) t Q (realWeightedHash weights), v.val = x ∧
        Good (graph t Q (realWeightedHash weights)) v := by
  classical
  constructor
  · intro hx
    obtain ⟨hxunique, houtside⟩ := Finset.mem_filter.mp hx
    have hunique := (UniqueWordCount.mem_uniqueWords x).mp hxunique
    have hnotExceptional : ¬ FiniteConflictGraph.Exceptional t k
        (wordLabel Q (realWeightedHash weights)) x := by
      intro h
      exact houtside (Or.inl h)
    let v : Vertex (n := n) t Q (realWeightedHash weights) := ⟨x, hunique, hnotExceptional⟩
    refine ⟨v, rfl, ?_⟩
    by_contra hnot
    apply houtside
    exact Or.inr ⟨v, rfl, hnot⟩
  · rintro ⟨v, hv, hgood⟩
    apply Finset.mem_filter.mpr
    refine ⟨(UniqueWordCount.mem_uniqueWords x).mpr ?_, ?_⟩
    · simpa only [hv] using v.property.1
    · intro hbad
      rcases hbad with hexceptional | hobstruction
      · change FiniteConflictGraph.Exceptional t k
          (wordLabel Q (realWeightedHash weights)) x at hexceptional
        apply v.property.2
        simpa only [hv] using hexceptional
      · obtain ⟨w, hw, hnot⟩ := hobstruction
        have hwv : w = v := Subtype.ext (hw.trans hv.symm)
        subst w
        exact hnot hgood
end DeletionCode.GoodWordBridge
