-- Prove2me | solution 1 for DeletionCode.PaperProbability.labels_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:05:18.857921+00:00
-- url     : https://prove2.me/submissions/d89ea6e9-bd1b-4ad5-9c3f-36b0aae6a832

import Definitions.Def_DeletionCode_NonseparatedFamily
import Definitions.Def_DeletionCode_ObstructionBound
import Definitions.Def_DeletionCode_PaperParameters
import Definitions.Def_DeletionCode_PaperProbability
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_end
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_zero
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_neg
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_ExceptionalProbability_mem_candidatePartners
import Theorems.Thm_DeletionCode_FiniteRelationBlocks_mem_selectedBlocks
import Theorems.Thm_DeletionCode_FiniteWalkRules_rational_step
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_empty
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_insert
import Theorems.Thm_DeletionCode_IntegerTorusMap_jointHash_apply
import Theorems.Thm_DeletionCode_PaperParameters_nine_le_L
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
attribute [local simp] DeletionCode.AlignmentTrace.Trace.matchedAnchor_end
attribute [local simp] DeletionCode.AlignmentTrace.Trace.matchedAnchor_zero
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
open DeletionCode DeletionCode.PaperProbability
open MeasureTheory Windows HeaderRecovery SignedSupport CircleUniform
open ExceptionalCountArithmetic ExceptionalProbability ObstructionProbability
open scoped ENNReal
namespace DeletionCode.PaperProbability
theorem _root_.solution (t n Q : ℕ) (hn : 1 ≤ n)
    (hQ : 8 * ObstructionBound.scale t n (PaperParameters.k n) ≤ Q) : 2 ≤ Q := by
  have hnp : 1 ≤ n ^ (2 * t - 1) := one_le_pow₀ hn
  have hLp : 1 ≤ (PaperParameters.L n) ^ (WitnessCost.exponent t) :=
    one_le_pow₀ (by have := PaperParameters.nine_le_L n; omega)
  have hs : 1 ≤ ObstructionBound.scale t n (PaperParameters.k n) := by
    simpa only [one_mul, ObstructionBound.scale, PaperParameters.L] using Nat.mul_le_mul hnp hLp
  omega
end DeletionCode.PaperProbability
