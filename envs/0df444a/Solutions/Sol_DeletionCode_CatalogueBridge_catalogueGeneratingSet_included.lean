-- Prove2me | solution 1 for DeletionCode.CatalogueBridge.catalogueGeneratingSet_included
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:50.615193+00:00
-- url     : https://prove2.me/submissions/9da84355-b9d3-40d2-8c1b-5a0fc818f58c

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedRuleCount
import Definitions.Def_DeletionCode_CatalogueBridge
import Theorems.Thm_DeletionCode_CatalogueBridge_valid_generatingRuleSet

set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueBridge
open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport
open RuleReconstruction SignedRuleCount DescriptionCount
namespace DeletionCode.CatalogueBridge
theorem _root_.solution (x : Letters) (n k ν R t c : ℕ)
    (group : Fin ν → Fin R) (Q : RuleSet k)
    (hQ : CatalogueGeneratingSet x n k ν R t c group Q) :
    GeneratingRuleSet x n k ν R c group Q := by
  obtain ⟨bubbles, hvalid, _, hgen, hc, rfl, _⟩ := hQ
  exact valid_generatingRuleSet bubbles group hvalid hgen hc
end DeletionCode.CatalogueBridge
