-- Prove2me | solution 1 for DeletionCode.ObstructionProbability.candidate_probability_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:04:06.461439+00:00
-- url     : https://prove2.me/submissions/04be26f4-1f93-4920-b35d-e6f57d228a2d

import Definitions.Def_DeletionCode_VerifiedConflictGraphWitness
import Definitions.Def_DeletionCode_WitnessCounting
import Definitions.Def_DeletionCode_RandomHash
import Definitions.Def_DeletionCode_ObstructionProbability
import Theorems.Thm_DeletionCode_ObstructionProbability_ruleTest_probability
import Theorems.Thm_DeletionCode_ObstructionProbability_candidateEvent_eq_union
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
import Theorems.Thm_DeletionCode_WalkSelection_ScanState_generating
import Theorems.Thm_DeletionCode_WitnessCounting_candidate_finite
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
theorem _root_.solution (t k Q R : ℕ) (ht : 1 ≤ t) (hR : 1 ≤ R)
    (x : Bits n) (hx : KUnique (padBits x) n k) (hQ : 2 ≤ Q) :
    realWeights (Gram (windowLength k)) (candidateEvent t k Q R x) ≤
      (Nat.card {U : RuleSet k // Candidate t (padBits x) n k R U} : ℝ≥0∞) *
        ENNReal.ofReal (2 / (Q : ℝ)) ^ R := by
  classical
  let := candidate_finite t ht (padBits x) n k R hR hx
  let : Fintype {U : RuleSet k // Candidate t (padBits x) n k R U} := Fintype.ofFinite _
  rw [candidateEvent_eq_union]
  calc
    _ ≤ ∑ U : {U : RuleSet k // Candidate t (padBits x) n k R U},
        realWeights (Gram (windowLength k)) (ruleTestEvent k Q U.val) :=
      measure_iUnion_fintype_le _ _
    _ = ∑ _U : {U : RuleSet k // Candidate t (padBits x) n k R U},
        ENNReal.ofReal (2 / (Q : ℝ)) ^ R := by
      apply Finset.sum_congr rfl
      intro U _hU
      rw [ruleTest_probability k Q hQ U.val U.property.independent, U.property.generating.1]
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
end DeletionCode.ObstructionProbability
