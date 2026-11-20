-- Prove2me | solution 1 for DeletionCode.ConnectedBlocks.RuleAdjacent.symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:19:38.411182+00:00
-- url     : https://prove2.me/submissions/22d305c1-f9b1-4436-99b5-4d1f60506657

import Definitions.Def_DeletionCode_ComponentBounds
import Definitions.Def_DeletionCode_CatalogueBridge
import Definitions.Def_DeletionCode_FiniteConnectedGrowth
import Definitions.Def_DeletionCode_ConnectedBlocks

set_option autoImplicit true
open DeletionCode DeletionCode.ConnectedBlocks
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport SignedRuleCount RuleReconstruction RuleSetGraph
namespace DeletionCode.ConnectedBlocks
namespace RuleAdjacent
theorem _root_.solution {L : ℕ} {w u : Gram L → ℤ}
    (h : RuleAdjacent w u) : RuleAdjacent u w := by
  obtain ⟨v, hw, hu⟩ := h
  exact ⟨v, hu, hw⟩
end RuleAdjacent
end DeletionCode.ConnectedBlocks
