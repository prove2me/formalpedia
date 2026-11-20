-- Prove2me | solution 1 for DeletionCode.FiniteRelationBlocks.relation_support_included
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:25:59.105877+00:00
-- url     : https://prove2.me/submissions/f3c082a2-e902-417d-9bff-38b5ef66bea5

import Definitions.Def_DeletionCode_RelationBlockSupport
import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_RelationBlockSavings
import Definitions.Def_DeletionCode_FiniteRelationBlocks
import Theorems.Thm_DeletionCode_FiniteRelationBlocks_mem_selectedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
attribute [local simp] DeletionCode.BlockPartition.mem_attachedBlocks
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blocks
attribute [local simp] DeletionCode.ComponentFibers.mem_fiber
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk


attribute [local simp] DeletionCode.FiniteRelationBlocks.mem_selectedBlocks

set_option autoImplicit true
open DeletionCode DeletionCode.FiniteRelationBlocks
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph BlockPartition
open scoped BigOperators
namespace DeletionCode.FiniteRelationBlocks
theorem _root_.solution {k : ℕ} (G I : RuleSet k) (hIG : I ⊆ G)
    (w : Gram (windowLength k) → ℤ)
    (a : (Gram (windowLength k) → ℤ) → ℚ)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ)) :
    SupportInclusion.CoordinateSupportIncluded {w} G := by
  classical
  intro g hg
  obtain ⟨z, hz, hzg⟩ := hg
  have hzw : z = w := Finset.mem_singleton.mp hz
  subst z
  by_contra hnone
  push Not at hnone
  have hzero : (w g : ℚ) = 0 := by
    rw [hrel g]
    apply Finset.sum_eq_zero
    intro u hu
    simp [hnone u (hIG hu)]
  exact hzg (by exact_mod_cast hzero)
end DeletionCode.FiniteRelationBlocks
