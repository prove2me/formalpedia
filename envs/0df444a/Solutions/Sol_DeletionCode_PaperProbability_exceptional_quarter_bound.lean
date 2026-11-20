-- Prove2me | solution 1 for DeletionCode.PaperProbability.exceptional_quarter_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:17:38.481657+00:00
-- url     : https://prove2.me/submissions/d057068b-7098-40f9-86e3-8b2e8e7b582a

import Definitions.Def_DeletionCode_NonseparatedFamily
import Definitions.Def_DeletionCode_ObstructionBound
import Definitions.Def_DeletionCode_PaperParameters
import Definitions.Def_DeletionCode_PaperProbability
import Theorems.Thm_DeletionCode_PaperProbability_labels_ge_two
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_end
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_zero
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
import Theorems.Thm_DeletionCode_NonseparatedFamily_exceptional_measure_le
import Theorems.Thm_DeletionCode_ObstructionBound_survival_term_le
import Theorems.Thm_DeletionCode_PaperParameters_nine_le_L
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
import Theorems.Thm_DeletionCode_WitnessCost_exponent_ge_two
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
theorem _root_.solution {n : ℕ} (t Q : ℕ) (x : Bits n)
    (hx : KUnique (padBits x) n (PaperParameters.k n))
    (hfit : PaperParameters.L n ≤ n)
    (hconstant : exceptionalConstant t ≤ PaperParameters.L n)
    (hQ : 8 * ObstructionBound.scale t n (PaperParameters.k n) ≤ Q) :
    realWeights (Gram (PaperParameters.L n))
        (exceptionalEvent t (PaperParameters.k n) Q x) ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
  have hL : 1 ≤ PaperParameters.L n := by have := PaperParameters.nine_le_L n; omega
  have hn : 1 ≤ n := hL.trans hfit
  have hQtwo := labels_ge_two t n Q hn hQ
  have hCL : exceptionalConstant t * PaperParameters.L n ≤
      (PaperParameters.L n) ^ (WitnessCost.exponent t) := by
    calc
      _ ≤ PaperParameters.L n * PaperParameters.L n := Nat.mul_le_mul_right _ hconstant
      _ = (PaperParameters.L n) ^ 2 := (pow_two _).symm
      _ ≤ _ := pow_le_pow_right₀ hL (WitnessCost.exponent_ge_two t)
  let C := exceptionalConstant t * PaperParameters.L n * n ^ (2 * t - 1)
  have hC : C ≤ ObstructionBound.scale t n (PaperParameters.k n) := by
    calc
      _ ≤ (PaperParameters.L n) ^ (WitnessCost.exponent t) * n ^ (2 * t - 1) :=
        Nat.mul_le_mul_right _ hCL
      _ = _ := by unfold ObstructionBound.scale PaperParameters.L; ring
  have h8 : 8 * C ≤ Q := (Nat.mul_le_mul_left 8 hC).trans hQ
  have hp := ObstructionBound.survival_term_le C C Q 1 (by simp) h8 (by omega)
  simp only [pow_one] at hp
  exact (NonseparatedFamily.exceptional_measure_le t (PaperParameters.k n) Q x hx hfit hQtwo).trans hp
end DeletionCode.PaperProbability
