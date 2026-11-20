-- Prove2me | solution 1 for DeletionCode.FiniteWalkRules.novelty_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:38:30.674154+00:00
-- url     : https://prove2.me/submissions/a97e474b-665e-474f-93d3-0afcf75a7b1f

import Definitions.Def_DeletionCode_WalkSelection
import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Definitions.Def_DeletionCode_FiniteWalkRules
import Theorems.Thm_DeletionCode_FiniteWalkRules_rational_step
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_empty
import Theorems.Thm_DeletionCode_FiniteWalkRules_selectedRules_insert
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_neg
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
attribute [local simp] DeletionCode.BlockPartition.mem_attachedBlocks
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blocks
attribute [local simp] DeletionCode.CatalogueAlgebra.rational_neg
attribute [local simp] DeletionCode.CatalogueAlgebra.rational_zero
attribute [local simp] DeletionCode.ComponentFibers.mem_fiber
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk


attribute [local simp] DeletionCode.FiniteWalkRules.rational_step
attribute [local simp] DeletionCode.FiniteWalkRules.selectedRules_empty
attribute [local simp] DeletionCode.FiniteWalkRules.selectedRules_insert

set_option autoImplicit true
open DeletionCode DeletionCode.FiniteWalkRules
open HeaderRecovery SignedSupport SignedRuleCount
open CatalogueAlgebra WalkSelection FiniteGenerating
variable {k m : ℕ}
namespace DeletionCode.FiniteWalkRules
theorem _root_.solution
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ) (S : Finset (Fin m))
    (i : Fin m)
    (hnew : ¬ SignedMember (walkStep (rationalPath p)) S (walkStep (rationalPath p) i)) :
    ∀ u ∈ selectedRules p S, step p i ≠ u ∧ step p i ≠ -u := by
  intro u hu
  obtain ⟨r, hr, rfl⟩ := (mem_selectedRules p S u).mp hu
  constructor
  · intro heq
    apply hnew
    refine ⟨r, hr, Or.inl ?_⟩
    simpa only [rational_step] using congrArg rational heq
  · intro heq
    apply hnew
    refine ⟨r, hr, Or.inr ?_⟩
    simpa only [rational_neg, rational_step] using congrArg rational heq
end DeletionCode.FiniteWalkRules
