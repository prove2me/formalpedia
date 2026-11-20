-- Prove2me | solution 1 for DeletionCode.CatalogueFamily.PresentedFamily.component_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:22:28.564169+00:00
-- url     : https://prove2.me/submissions/2759acba-c0ae-47e0-8a87-a374ced9c2c6

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_CanonicalIndex
import Definitions.Def_DeletionCode_CatalogueFamily
import Theorems.Thm_DeletionCode_CatalogueBridge_ValidCatalogue_geometry
import Theorems.Thm_DeletionCode_RuleSetGraph_componentCount_rulesOfFamily


set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueFamily
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport SignedRuleCount RuleReconstruction RuleSetGraph SupportComponents
open CanonicalIndex ConnectedBlocks
open scoped BigOperators
open DeletionCode.CatalogueFamily.PresentedFamily
variable {t k R : ℕ} {G : Fin R → Gram (windowLength k) → ℤ}
namespace DeletionCode.CatalogueFamily.PresentedFamily
theorem _root_.solution (P : PresentedFamily t k R G) :
    componentCount (Finset.univ.image G) =
      Fintype.card (GraphComponents P.E.family (windowLength k)) := by
  rw [← P.rule_set]
  exact componentCount_rulesOfFamily P.E (CanonicalIndex.group t R) P.rank P.geometry P.disjoint
end DeletionCode.CatalogueFamily.PresentedFamily
