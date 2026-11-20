-- Prove2me | solution 1 for DeletionCode.ObstructionProbability.obstructionEvent_subset_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:18:53.94868+00:00
-- url     : https://prove2.me/submissions/b7cc559e-bcde-4830-ab41-b458134fac66

import Definitions.Def_DeletionCode_VerifiedConflictGraphWitness
import Definitions.Def_DeletionCode_WitnessCounting
import Definitions.Def_DeletionCode_RandomHash
import Definitions.Def_DeletionCode_ObstructionProbability
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
import Theorems.Thm_DeletionCode_IntegerTorusMap_jointHash_apply
import Theorems.Thm_DeletionCode_RandomHash_independent
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
import Theorems.Thm_DeletionCode_VerifiedConflictGraphWitness_bounded_witness
import Theorems.Thm_DeletionCode_WalkSelection_ScanState_generating
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
attribute [local simp] DeletionCode.IntegerTorusMap.jointHash_apply
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk



set_option autoImplicit true
open DeletionCode DeletionCode.ObstructionProbability
open MeasureTheory Windows HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph
open CircleHash CircleUniform ConflictGraphWitness WitnessCounting
open scoped BigOperators ENNReal
variable {n : ℕ}
namespace DeletionCode.ObstructionProbability
theorem _root_.solution (t k Q : ℕ) (ht : 2 ≤ t) (hQ : 2 ≤ Q)
    (x : Bits n) :
    obstructionEvent t k Q x ⊆
      ⋃ R ∈ Finset.Icc 2 (cutoff t k), candidateEvent t k Q R x := by
  intro weights hbad
  obtain ⟨v, hv, hnot⟩ := hbad
  obtain ⟨U, hU, hgen⟩ :=
    VerifiedConflictGraphWitness.bounded_witness ht hQ (realWeightedHash weights) v hnot
  apply Set.mem_iUnion.mpr
  refine ⟨U.card, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_Icc.mpr ⟨hU.bounds.size_lower, hU.bounds.size_upper⟩
  · refine ⟨U, ⟨?_, hU.bounds, hU.generating.independent⟩, ?_⟩
    · simpa only [hv] using hgen
    · intro u hu
      exact (hU.surviving u hu).2
end DeletionCode.ObstructionProbability
