-- Prove2me | solution 1 for DeletionCode.ExceptionalProbability.exceptional_probability_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:56:04.668629+00:00
-- url     : https://prove2.me/submissions/44a517f8-d687-4982-83ae-5aef22cc8863

import Definitions.Def_DeletionCode_RandomHash
import Definitions.Def_DeletionCode_ConflictGraphWitness
import Definitions.Def_DeletionCode_SpectrumPath
import Definitions.Def_DeletionCode_ExceptionalProbability
import Theorems.Thm_DeletionCode_ExceptionalProbability_mem_candidatePartners
import Theorems.Thm_DeletionCode_ExceptionalProbability_collision_probability_le
import Theorems.Thm_DeletionCode_ExceptionalProbability_exceptionalEvent_eq_union
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
attribute [local simp] DeletionCode.IntegerTorusMap.jointHash_apply
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk


attribute [local simp] DeletionCode.ExceptionalProbability.mem_candidatePartners

set_option autoImplicit true
open DeletionCode DeletionCode.ExceptionalProbability
open MeasureTheory Windows HeaderRecovery SignedSupport CircleHash CircleUniform
open ConflictGraphWitness
open scoped BigOperators
variable {n : ℕ}
namespace DeletionCode.ExceptionalProbability
theorem _root_.solution (t k Q : ℕ) (x : Bits n)
    (hx : KUnique (padBits x) n k) (hn : windowLength k ≤ n) (hQ : 2 ≤ Q) :
    realWeights (Gram (windowLength k))
        {weights | FiniteConflictGraph.Exceptional t k
          (wordLabel Q (realWeightedHash weights)) x} ≤
      (candidatePartners t k x).card * ENNReal.ofReal (2 / (Q : ℝ)) := by
  classical
  change realWeights (Gram (windowLength k)) (exceptionalEvent t k Q x) ≤ _
  rw [exceptionalEvent_eq_union t k Q x hx]
  calc
    _ ≤ ∑ y ∈ candidatePartners t k x,
        realWeights (Gram (windowLength k)) (collisionEvent k Q x y) :=
      measure_biUnion_finset_le (candidatePartners t k x) (collisionEvent k Q x)
    _ ≤ ∑ _y ∈ candidatePartners t k x, ENNReal.ofReal (2 / (Q : ℝ)) := by
      apply Finset.sum_le_sum
      intro y hy
      exact collision_probability_le k Q x y hx hn hQ
        ((mem_candidatePartners t k x y).mp hy).1
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
end DeletionCode.ExceptionalProbability
