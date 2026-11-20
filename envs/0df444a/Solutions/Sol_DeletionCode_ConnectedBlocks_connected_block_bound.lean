-- Prove2me | solution 1 for DeletionCode.ConnectedBlocks.connected_block_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:23:31.520254+00:00
-- url     : https://prove2.me/submissions/4ef51212-683c-4ae4-891b-c79e96130cf4

import Definitions.Def_DeletionCode_ComponentBounds
import Definitions.Def_DeletionCode_CatalogueBridge
import Definitions.Def_DeletionCode_FiniteConnectedGrowth
import Definitions.Def_DeletionCode_ConnectedBlocks
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm
import Theorems.Thm_DeletionCode_ConnectedBlocks_catalogue_singleton_component_count_le
import Theorems.Thm_DeletionCode_ConnectedBlocks_adjoining_rule_component_sum
import Theorems.Thm_DeletionCode_FiniteConnectedGrowth_connected_count_bound


set_option autoImplicit true
open DeletionCode DeletionCode.ConnectedBlocks
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport SignedRuleCount RuleReconstruction RuleSetGraph
namespace DeletionCode.ConnectedBlocks
theorem _root_.solution {t k : ℕ} (ht : 1 ≤ t) (B : RuleSet k)
    (hB : B.Nonempty) (hcatalogue : ∀ w ∈ B, CatalogueRule t k w)
    (hconnected : Connected B) :
    componentCount B ≤ (2 * t - 1) * B.card + 1 := by
  classical
  apply FiniteConnectedGrowth.connected_count_bound B RuleAdjacent hB hconnected
    componentCount (2 * t) (by omega)
  · intro w hw
    exact catalogue_singleton_component_count_le w (hcatalogue w hw)
  · intro U hUB w hwB _ hadj
    apply adjoining_rule_component_sum U w (hcatalogue w hwB)
    obtain ⟨u, hu, hwu | huw⟩ := hadj
    · exact ⟨u, hu, hwu⟩
    · exact ⟨u, hu, huw.symm⟩
end DeletionCode.ConnectedBlocks
