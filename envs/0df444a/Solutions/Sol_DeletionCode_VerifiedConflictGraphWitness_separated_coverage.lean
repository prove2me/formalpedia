-- Prove2me | solution 1 for DeletionCode.VerifiedConflictGraphWitness.separated_coverage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:15:21.830013+00:00
-- url     : https://prove2.me/submissions/8d5a36d6-c4a4-43f2-abc5-50d4ea72f78d

import Definitions.Def_DeletionCode_ConflictGraphWitness
import Definitions.Def_DeletionCode_BubbleCatalogue
import Definitions.Def_DeletionCode_SeparatedTraceCoverage
import Definitions.Def_DeletionCode_VerifiedConflictGraphWitness
import Theorems.Thm_DeletionCode_VerifiedConflictGraphWitness_listLetters_ofFn
import Theorems.Thm_DeletionCode_VerifiedConflictGraphWitness_unique_zero_length
import Theorems.Thm_DeletionCode_VerifiedConflictGraphWitness_empty_catalogue
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_end
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_zero
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_source_length
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_BubbleCatalogue_catalogueRule
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_neg
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_FiniteRelationBlocks_mem_selectedBlocks
import Theorems.Thm_DeletionCode_FiniteWalkRules_rational_step
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_empty
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_insert
import Theorems.Thm_DeletionCode_SeparatedTraceCoverage_catalogueRule
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
open DeletionCode DeletionCode.VerifiedConflictGraphWitness
open Windows HeaderRecovery CatalogueWords AlignmentTrace
open ConflictGraphWitness SignedSupport SignedRuleCount RuleSetGraph WitnessCases
namespace DeletionCode.VerifiedConflictGraphWitness
theorem _root_.solution (t k n : ℕ) : SeparatedCoverage t k n := by
  intro x y hx trace hs ht hd hi hsep
  by_cases hk : 1 ≤ k
  · have hx' : KUnique (listLetters trace.source) trace.source.length k := by
      simpa only [hs, List.length_ofFn, listLetters_ofFn] using hx
    have h := SeparatedTraceCoverage.catalogueRule trace t k hk hx' hsep hd hi
    simpa only [hs, ht, List.length_ofFn, listLetters_ofFn, spectrum] using h
  · have hk0 : k = 0 := by omega
    subst k
    have hn := unique_zero_length hx
    have hlen : trace.source.length = n := by rw [hs, List.length_ofFn]
    have hc := trace.source_length
    have ht0 : t = 0 := by omega
    rw [ht0]
    subst n
    have hxy : x = y := Subsingleton.elim _ _
    rw [hxy, sub_self]
    exact empty_catalogue 0
end DeletionCode.VerifiedConflictGraphWitness
