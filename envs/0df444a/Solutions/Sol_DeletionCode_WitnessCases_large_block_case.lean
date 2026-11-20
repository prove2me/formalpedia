-- Prove2me | solution 1 for DeletionCode.WitnessCases.large_block_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:34:01.400861+00:00
-- url     : https://prove2.me/submissions/be863236-62cc-438c-85a8-b4c35436102a

import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_FiniteRelationBlocks
import Definitions.Def_DeletionCode_SupportBlockCount
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Definitions.Def_DeletionCode_LargeBlockSelection
import Definitions.Def_DeletionCode_WitnessCases
import Theorems.Thm_DeletionCode_BlockAdjunction_new_block_card_bound
import Theorems.Thm_DeletionCode_BlockAdjunction_new_block_component_bound
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_neg
import Theorems.Thm_DeletionCode_CatalogueAlgebra_rational_zero
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_FiniteGenerating_generating_blockOf
import Theorems.Thm_DeletionCode_FiniteRelationBlocks_mem_selectedBlocks
import Theorems.Thm_DeletionCode_LargeBlockSelection_new_block_large_of_exists
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
theorem _root_.solution {t k : ℕ} (ht : 2 ≤ t)
    (v : Gram (windowLength k) → ℤ) (K : Set (Gram (windowLength k) → ℤ))
    (G : RuleSet k) (w : Gram (windowLength k) → ℤ)
    (hgen : GeneratingAt v (insert w G)) (hw : CatalogueRule t k w)
    (hcat : ∀ u ∈ G, CatalogueRule t k u)
    (hK : ∀ u ∈ insert w G, u ∈ K)
    (hsize : ∀ B ∈ blocks G, B.card ≤ windowLength k)
    (hbad : ¬ ∀ B ∈ blocks (insert w G), B.card ≤ windowLength k) :
    Witness t k v K (blockOf (insert w G) w) := by
  classical
  have hex : ∃ B ∈ blocks (insert w G), windowLength k < B.card := by
    push Not at hbad
    exact hbad
  have hlarge := LargeBlockSelection.new_block_large_of_exists G w (windowLength k) hsize hex
  have hL : 2 ≤ windowLength k := by unfold windowLength; omega
  have hlow : 2 ≤ (blockOf (insert w G) w).card := hL.trans (Nat.le_of_lt hlarge)
  have hupper := BlockAdjunction.new_block_card_bound G w hw hsize
  have hc := BlockAdjunction.new_block_component_bound (by omega : 1 ≤ t) G w hw hcat
  refine ⟨generating_blockOf hgen w, ?_, ?_, hlow, hupper, hc, ?_⟩
  · intro u hu
    rcases Finset.mem_insert.mp ((mem_blockOf (insert w G) w u).mp hu).1 with huw | huG
    · simpa only [huw] using hw
    · exact hcat u huG
  · intro u hu
    exact hK u ((mem_blockOf (insert w G) w u).mp hu).1
  · intro hsmall
    omega
end DeletionCode.WitnessCases
