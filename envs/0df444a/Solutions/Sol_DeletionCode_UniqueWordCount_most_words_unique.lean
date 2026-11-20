-- Prove2me | solution 1 for DeletionCode.UniqueWordCount.most_words_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:56:55.094876+00:00
-- url     : https://prove2.me/submissions/77901b03-25b4-4317-a2e4-7edc3fd75107

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_OverlapCollision
import Definitions.Def_DeletionCode_FinitePairUnion
import Definitions.Def_DeletionCode_UniqueWordParameters
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_DeletionCode_UniqueWordCount
import Theorems.Thm_DeletionCode_UniqueWordCount_card_unique_lower_bound
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
import Theorems.Thm_DeletionCode_UniqueWordParameters_half_words_le_seven_eighths
import Theorems.Thm_DeletionCode_UniqueWordParameters_seven_eighths_le_retained
import Theorems.Thm_DeletionCode_UniqueWordParameters_uniquenessLength_ge_two
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
open DeletionCode DeletionCode.UniqueWordCount
open Windows HeaderRecovery
attribute [local instance] Classical.propDecidable
namespace DeletionCode.UniqueWordCount
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) :
    let k := UniqueWordParameters.uniquenessLength n
    (1 - (n.choose 2 : ℚ) / (2 : ℚ) ^ k) * (2 : ℚ) ^ n ≤ (uniqueWords n k).card ∧
    (7 / 8 : ℚ) * (2 : ℚ) ^ n ≤ (1 - (n.choose 2 : ℚ) / (2 : ℚ) ^ k) * (2 : ℚ) ^ n ∧
    (2 : ℚ) ^ (n - 1) ≤ (7 / 8 : ℚ) * (2 : ℚ) ^ n := by
  dsimp
  exact ⟨card_unique_lower_bound n _ (by
      have h := UniqueWordParameters.uniquenessLength_ge_two n
      omega),
    UniqueWordParameters.seven_eighths_le_retained n,
    UniqueWordParameters.half_words_le_seven_eighths n hn⟩
end DeletionCode.UniqueWordCount
