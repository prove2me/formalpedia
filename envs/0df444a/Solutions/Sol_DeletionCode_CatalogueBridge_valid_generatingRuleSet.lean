-- Prove2me | solution 1 for DeletionCode.CatalogueBridge.valid_generatingRuleSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:58.022982+00:00
-- url     : https://prove2.me/submissions/7122b232-e471-443c-9a2f-fdb5ba64a345

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedRuleCount
import Definitions.Def_DeletionCode_CatalogueBridge
import Theorems.Thm_DeletionCode_CatalogueBridge_ValidCatalogue_geometry
import Theorems.Thm_DeletionCode_CatalogueBridge_ValidCatalogue_rank_disjoint

set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueBridge
open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport
open RuleReconstruction SignedRuleCount DescriptionCount
namespace DeletionCode.CatalogueBridge
theorem _root_.solution {k ν R n c : ℕ} {x : Letters}
    (bubbles : Fin ν → BubbleWord k) (group : Fin ν → Fin R)
    (hvalid : ValidCatalogue bubbles group)
    (hgen : SignedGenerating (indexedFamily bubbles group).family x n (windowLength k))
    (hc : Fintype.card
      (SupportComponents.GraphComponents (indexedFamily bubbles group).family (windowLength k)) = c) :
    GeneratingRuleSet x n k ν R c group (rulesOfFamily (indexedFamily bubbles group) group) := by
  exact ⟨indexedFamily bubbles group, fun _ => rfl, hvalid.geometry,
    hvalid.rank_disjoint, hgen, hc, rfl⟩
end DeletionCode.CatalogueBridge
