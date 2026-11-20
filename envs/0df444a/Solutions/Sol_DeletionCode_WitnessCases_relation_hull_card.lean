-- Prove2me | solution 1 for DeletionCode.WitnessCases.relation_hull_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:35:33.322714+00:00
-- url     : https://prove2.me/submissions/d050ea7f-fda1-40ba-a946-9597a06359e8

import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_FiniteRelationBlocks
import Definitions.Def_DeletionCode_SupportBlockCount
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Definitions.Def_DeletionCode_LargeBlockSelection
import Definitions.Def_DeletionCode_WitnessCases
import Theorems.Thm_DeletionCode_WitnessCases_relation_block_count
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_neg
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_FiniteRelationBlocks_mem_selectedBlocks
import Theorems.Thm_DeletionCode_FiniteRelationBlocks_selectedBlocks_biUnion
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
attribute [local simp] DeletionCode.BlockPartition.mem_attachedBlocks
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blocks
attribute [local simp] DeletionCode.CatalogueAlgebra.rational_neg
attribute [local simp] DeletionCode.CatalogueAlgebra.rational_zero
attribute [local simp] DeletionCode.ComponentFibers.mem_fiber
attribute [local simp] DeletionCode.FiniteRelationBlocks.mem_selectedBlocks
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk



set_option autoImplicit true
open DeletionCode DeletionCode.WitnessCases
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition FiniteGenerating FiniteRelationBlocks CatalogueAlgebra
open scoped BigOperators
namespace DeletionCode.WitnessCases
theorem _root_.solution {t k : ℕ} (G I : RuleSet k) (hIG : I ⊆ G)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (a : (Gram (windowLength k) → ℤ) → ℚ) (hind : Independent G)
    (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ))
    (hsize : ∀ B ∈ blocks G, B.card ≤ windowLength k) :
    (RelationBlockSavings.blockHull G I).card ≤ 2 * t * windowLength k := by
  classical
  rw [← selectedBlocks_biUnion G I hIG]
  calc
    ((selectedBlocks G I).biUnion id).card ≤ ∑ B ∈ selectedBlocks G I, B.card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _B ∈ selectedBlocks G I, windowLength k := by
      apply Finset.sum_le_sum
      intro B hB
      exact hsize B ((mem_selectedBlocks G I B).mp hB).1
    _ = (selectedBlocks G I).card * windowLength k := by simp
    _ ≤ 2 * t * windowLength k := Nat.mul_le_mul_right _
      (relation_block_count G I hIG w hw a hind ha hrel)
end DeletionCode.WitnessCases
