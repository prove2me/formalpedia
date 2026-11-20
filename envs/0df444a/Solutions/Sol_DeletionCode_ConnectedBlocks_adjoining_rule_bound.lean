-- Prove2me | solution 1 for DeletionCode.ConnectedBlocks.adjoining_rule_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:23:31.046647+00:00
-- url     : https://prove2.me/submissions/839fbc3c-ce42-4d73-aca5-ede9543d04c7

import Definitions.Def_DeletionCode_ComponentBounds
import Definitions.Def_DeletionCode_CatalogueBridge
import Definitions.Def_DeletionCode_FiniteConnectedGrowth
import Definitions.Def_DeletionCode_ConnectedBlocks
import Theorems.Thm_DeletionCode_ConnectedBlocks_adjoining_rule_component_sum

set_option autoImplicit true
open DeletionCode DeletionCode.ConnectedBlocks
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport SignedRuleCount RuleReconstruction RuleSetGraph
namespace DeletionCode.ConnectedBlocks
theorem _root_.solution {t k : ℕ} (ht : 1 ≤ t)
    (U : RuleSet k) (w : Gram (windowLength k) → ℤ)
    (hw : CatalogueRule t k w) (hadj : ∃ u ∈ U, RuleAdjacent w u) :
    componentCount (insert w U) ≤ componentCount U + (2 * t - 1) := by
  have h := adjoining_rule_component_sum U w hw hadj
  omega
end DeletionCode.ConnectedBlocks
