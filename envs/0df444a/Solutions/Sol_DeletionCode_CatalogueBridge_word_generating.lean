-- Prove2me | solution 1 for DeletionCode.CatalogueBridge.word_generating
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:58.495372+00:00
-- url     : https://prove2.me/submissions/b7bb5ceb-c9f1-4907-8869-38fd4671c97a

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedRuleCount
import Definitions.Def_DeletionCode_CatalogueBridge
import Theorems.Thm_DeletionCode_CatalogueBridge_ValidCatalogue_geometry
import Theorems.Thm_DeletionCode_CatalogueBridge_ValidCatalogue_rank_disjoint
import Theorems.Thm_DeletionCode_SignedSupport_signed_generating_implies_generating


set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueBridge
open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport
open RuleReconstruction SignedRuleCount DescriptionCount
namespace DeletionCode.CatalogueBridge
theorem _root_.solution {k ν R n : ℕ} {x : Letters}
    (bubbles : Fin ν → BubbleWord k) (group : Fin ν → Fin R)
    (hvalid : ValidCatalogue bubbles group)
    (hgen : SignedGenerating (indexedFamily bubbles group).family x n (windowLength k)) :
    (indexedFamily bubbles group).family.Generating x n (windowLength k) :=
  signed_generating_implies_generating (indexedFamily bubbles group).family x n
    (windowLength k) hvalid.geometry hvalid.rank_disjoint hgen
end DeletionCode.CatalogueBridge
