-- Prove2me | solution 1 for DeletionCode.CatalogueBridge.ValidCatalogue.geometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:04.544181+00:00
-- url     : https://prove2.me/submissions/e57da789-1ad1-4716-b2ce-cdb07886a86e

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedRuleCount
import Definitions.Def_DeletionCode_CatalogueBridge
import Theorems.Thm_DeletionCode_CatalogueBridge_differentLengths

set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueBridge
open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport
open RuleReconstruction SignedRuleCount DescriptionCount
namespace DeletionCode.CatalogueBridge
namespace ValidCatalogue
theorem _root_.solution {k ν R : ℕ}
    {bubbles : Fin ν → BubbleWord k} {group : Fin ν → Fin R}
    (h : ValidCatalogue bubbles group) :
    BubbleGeometry (indexedFamily bubbles group).family (windowLength k) :=
  ⟨h.simple, h.endpoints, differentLengths (indexedFamily bubbles group)⟩
end ValidCatalogue
end DeletionCode.CatalogueBridge
