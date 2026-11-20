-- Prove2me | solution 1 for DeletionCode.CodeExistence.exists_large_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:36:02.555245+00:00
-- url     : https://prove2.me/submissions/a8fb8f6c-d660-44fc-b1a4-b9fa93067334

import Definitions.Def_DeletionCode_PaperProbability
import Definitions.Def_DeletionCode_FiniteDiscard
import Definitions.Def_DeletionCode_GoodWordBridge
import Definitions.Def_DeletionCode_RedundancyBounds
import Definitions.Def_DeletionCode_CodeExistence
import Theorems.Thm_DeletionCode_CodeExistence_labelCount_eq_scale
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_end
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_zero
import Theorems.Thm_DeletionCode_BipartiteSelection_mem_goodVertices
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_neg
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
import Theorems.Thm_DeletionCode_CodeSelection_exists_correcting_code
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_EditAlignment_Script_trans
import Theorems.Thm_DeletionCode_ExceptionalProbability_mem_candidatePartners
import Theorems.Thm_DeletionCode_FiniteDiscard_exists_half_retained
import Theorems.Thm_DeletionCode_FiniteRelationBlocks_mem_selectedBlocks
import Theorems.Thm_DeletionCode_FiniteWalkRules_rational_step
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_empty
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_insert
import Theorems.Thm_DeletionCode_GoodWordBridge_card_retainedWords
import Theorems.Thm_DeletionCode_IntegerTorusMap_jointHash_apply
import Theorems.Thm_DeletionCode_PaperParameters_threshold
import Theorems.Thm_DeletionCode_PaperProbability_labels_ge_two
import Theorems.Thm_DeletionCode_PaperProbability_total_discard_le
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
import Theorems.Thm_DeletionCode_UniqueWordCount_half_words_le_card_unique
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
open DeletionCode DeletionCode.CodeExistence
open HeaderRecovery Windows SignedSupport CircleUniform CircleHash
open ExceptionalProbability ObstructionProbability CodeSelection
namespace DeletionCode.CodeExistence
theorem _root_.solution (t n : ℕ) (ht : 2 ≤ t) (hn : 1 ≤ n)
    (hfit : PaperParameters.L n ≤ n)
    (hready : PaperProbability.threshold t ≤ PaperParameters.L n) :
    ∃ C : Finset (Bits n), Corrects t C ∧
      2 ^ n ≤ 8 * RedundancyBounds.labelCount t n * C.card := by
  classical
  let Q := RedundancyBounds.labelCount t n
  have hQ : 8 * ObstructionBound.scale t n (PaperParameters.k n) ≤ Q := by
    dsimp only [Q]
    rw [labelCount_eq_scale]
  have hQtwo : 2 ≤ Q := PaperProbability.labels_ge_two t n Q hn hQ
  let s := UniqueWordCount.uniqueWords n (PaperParameters.k n)
  let E := fun x : Bits n =>
    exceptionalEvent t (PaperParameters.k n) Q x ∪
      obstructionEvent t (PaperParameters.k n) Q x
  obtain ⟨weights, hhalf⟩ := FiniteDiscard.exists_half_retained
    (realWeights (Gram (windowLength (PaperParameters.k n)))) s E (by
      intro x hx
      have h := PaperProbability.total_discard_le t Q ht x
        ((UniqueWordCount.mem_uniqueWords x).mp hx) hfit hready hQ
      unfold PaperParameters.L at h
      exact h)
  have hhalf' : s.card ≤ 2 *
      (GoodWordBridge.retainedWords (n := n) t (PaperParameters.k n) Q weights).card := by
    simpa only [GoodWordBridge.retainedWords, s, E] using hhalf
  rw [GoodWordBridge.card_retainedWords] at hhalf'
  obtain ⟨C, hselect, hcorrect⟩ := exists_correcting_code (n := n) t Q hQtwo
    (realWeightedHash weights)
  have hunique : 2 ^ (n - 1) ≤ s.card := UniqueWordCount.half_words_le_card_unique n hn
  have hpow : (2 : ℕ) ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [pow_succ, Nat.mul_comm]
  refine ⟨C, hcorrect, ?_⟩
  change 2 ^ n ≤ 8 * Q * C.card
  calc
    2 ^ n = 2 * 2 ^ (n - 1) := hpow
    _ ≤ 2 * s.card := Nat.mul_le_mul_left 2 hunique
    _ ≤ 2 * (2 * (2 * Q * C.card)) :=
      Nat.mul_le_mul_left 2 (hhalf'.trans (Nat.mul_le_mul_left 2 hselect))
    _ = 8 * Q * C.card := by ring
end DeletionCode.CodeExistence
