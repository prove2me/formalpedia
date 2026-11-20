-- Prove2me | solution 1 for DeletionCode.CatalogueBridge.ValidCatalogue.rank_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:21.0712+00:00
-- url     : https://prove2.me/submissions/872c30c9-bdde-46ab-8ad3-6e3c7964cc70

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedRuleCount
import Definitions.Def_DeletionCode_CatalogueBridge

set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueBridge
open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport
open RuleReconstruction SignedRuleCount DescriptionCount
namespace DeletionCode.CatalogueBridge
namespace ValidCatalogue
theorem _root_.solution {k ν R : ℕ}
    {bubbles : Fin ν → BubbleWord k} {group : Fin ν → Fin R}
    (h : ValidCatalogue bubbles group) :
    ∀ i, VertexDisjointOn (indexedFamily bubbles group).family (windowLength k)
      (ruleBubbles (indexedFamily bubbles group).family i) := by
  intro i a ha b hb hab sa sb j l hj hl
  have hra := (Finset.mem_filter.mp ha).2
  have hrb := (Finset.mem_filter.mp hb).2
  change (group a).val = i at hra
  change (group b).val = i at hrb
  have hgroup : group b = group a := Fin.ext (hrb.trans hra.symm)
  exact h.within_rule_disjoint (group a) a (by simp) b (by simp [hgroup]) hab sa sb j l hj hl
end ValidCatalogue
end DeletionCode.CatalogueBridge
