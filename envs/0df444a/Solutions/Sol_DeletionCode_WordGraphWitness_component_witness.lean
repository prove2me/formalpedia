-- Prove2me | solution 1 for DeletionCode.WordGraphWitness.component_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:05:34.513831+00:00
-- url     : https://prove2.me/submissions/26c13151-0eb3-4ac2-bb18-7f7874cfabfe

import Definitions.Def_DeletionCode_OddGraphWalk
import Definitions.Def_DeletionCode_BoundedWitnessWalk
import Definitions.Def_DeletionCode_WordGraphWitness
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_BoundedWitnessWalk_extract_word_walk
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_neg
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_FiniteRelationBlocks_mem_selectedBlocks
import Theorems.Thm_DeletionCode_FiniteWalkRules_rational_step
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_empty
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_insert
import Theorems.Thm_DeletionCode_OddGraphWalk_component_odd_walk
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
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
open DeletionCode DeletionCode.WordGraphWitness
open Windows HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph
open ConnectedBlocks WitnessCases
namespace DeletionCode.WordGraphWitness
theorem _root_.solution {V : Type*} {t k n : ℕ} (ht : 2 ≤ t)
    (G : SimpleGraph V) (words : V → Letters)
    (K : Set (Gram (windowLength k) → ℤ))
    (hunique : ∀ v, KUnique (words v) n k)
    (hcat : ∀ {v w}, G.Adj v w → CatalogueRule t k
      (wordSpectrum (words w) n (windowLength k) -
        wordSpectrum (words v) n (windowLength k)))
    (hK : ∀ {v w}, G.Adj v w →
      (wordSpectrum (words w) n (windowLength k) -
        wordSpectrum (words v) n (windowLength k)) ∈ K)
    (x : V) (hnot : ¬ (G.connectedComponentMk x).toSimpleGraph.Colorable 2) :
    ∃ U : RuleSet k,
      Witness t k (wordSpectrum (words x) n (windowLength k)) K U ∧
      ManuscriptCounting.GeneratingSet t (words x) n k U.card (componentCount U) U := by
  obtain ⟨m, hodd, vertices, hstart, hend, hadj⟩ := OddGraphWalk.component_odd_walk x hnot
  let walkWords : Fin (m + 1) → Letters := fun j => words (vertices j)
  have hclosed : Agree (walkWords 0) 0 (walkWords (Fin.last m)) 0 n := by
    intro j _
    simp only [walkWords, hstart, hend]
  obtain ⟨U, hU, hcount⟩ := BoundedWitnessWalk.extract_word_walk ht walkWords K
    (fun j => hunique (vertices j)) hclosed hodd (fun i => hcat (hadj i))
    (fun i => hK (hadj i))
  exact ⟨U, by simpa only [walkWords, hstart] using hU,
    by simpa only [walkWords, hstart] using hcount⟩
end DeletionCode.WordGraphWitness
