-- Prove2me | solution 1 for DeletionCode.WitnessCases.relation_block_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:33:04.117854+00:00
-- url     : https://prove2.me/submissions/d4387915-69be-4e05-847a-c51113cb7c43

import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_FiniteRelationBlocks
import Definitions.Def_DeletionCode_SupportBlockCount
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Definitions.Def_DeletionCode_LargeBlockSelection
import Definitions.Def_DeletionCode_WitnessCases
import Theorems.Thm_DeletionCode_FiniteRelationBlocks_mem_selectedBlocks
import Theorems.Thm_DeletionCode_FiniteRelationBlocks_relation_support_included
import Theorems.Thm_DeletionCode_FiniteRelationBlocks_selected_block_meets
import Theorems.Thm_DeletionCode_SupportBlockCount_catalogue_block_count_le
attribute [local simp] DeletionCode.FiniteRelationBlocks.mem_selectedBlocks



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
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ)) :
    (selectedBlocks G I).card ≤ 2 * t := by
  apply SupportBlockCount.catalogue_block_count_le G w (selectedBlocks G I) hw
  · intro B hB
    exact ((mem_selectedBlocks G I B).mp hB).1
  · exact relation_support_included G I hIG w a hrel
  · exact selected_block_meets G I hIG w a hind ha hrel
end DeletionCode.WitnessCases
