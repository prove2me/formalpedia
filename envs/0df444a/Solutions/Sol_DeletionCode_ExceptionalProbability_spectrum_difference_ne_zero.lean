-- Prove2me | solution 1 for DeletionCode.ExceptionalProbability.spectrum_difference_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:48:03.2053+00:00
-- url     : https://prove2.me/submissions/6e5c0306-3944-42d3-895a-42c01c8ebae9

import Definitions.Def_DeletionCode_RandomHash
import Definitions.Def_DeletionCode_ConflictGraphWitness
import Definitions.Def_DeletionCode_SpectrumPath
import Definitions.Def_DeletionCode_ExceptionalProbability
import Theorems.Thm_DeletionCode_ExceptionalProbability_mem_candidatePartners
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_end
import Theorems.Thm_DeletionCode_AlignmentTrace_Trace_matchedAnchor_zero
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_neg
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm
import Theorems.Thm_DeletionCode_FiniteRelationBlocks_mem_selectedBlocks
import Theorems.Thm_DeletionCode_FiniteWalkRules_rational_step
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_empty
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_insert
import Theorems.Thm_DeletionCode_IntegerTorusMap_jointHash_apply
import Theorems.Thm_DeletionCode_SpectrumPath_equal_spectrum_recovers_word
import Theorems.Thm_DeletionCode_SpectrumPath_kunique_mono
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
theorem _root_.solution (k : ℕ) (x y : Bits n)
    (hx : KUnique (padBits x) n k) (hn : windowLength k ≤ n) (hxy : x ≠ y) :
    spectrum k y - spectrum k x ≠ 0 := by
  intro hzero
  have hs : wordSpectrum (padBits y) n (windowLength k) =
      wordSpectrum (padBits x) n (windowLength k) := sub_eq_zero.mp hzero
  have hlarge : k ≤ windowLength k - 1 := by
    dsimp [windowLength]
    omega
  have hagree := SpectrumPath.equal_spectrum_recovers_word (padBits x) (padBits y)
    n (windowLength k) (by dsimp [windowLength]; omega) hn
    (SpectrumPath.kunique_mono (padBits x) n k (windowLength k - 1) hx hlarge) hs
  have hyx : y = x := by
    funext i
    simpa only [Nat.zero_add, padBits, dif_pos i.isLt] using hagree i.val i.isLt
  exact hxy hyx.symm
end DeletionCode.ExceptionalProbability
