-- Prove2me | solution 1 for DeletionCode.CatalogueFamily.PresentedFamily.bubbleComponent_vertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:23:46.942079+00:00
-- url     : https://prove2.me/submissions/acd96bf7-1512-4ebf-ae30-0d94b8f91713

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_CanonicalIndex
import Definitions.Def_DeletionCode_CatalogueFamily
import Theorems.Thm_DeletionCode_CatalogueFamily_PresentedFamily_common_start
import Theorems.Thm_DeletionCode_CatalogueBridge_ValidCatalogue_geometry


set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueFamily
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport SignedRuleCount RuleReconstruction RuleSetGraph SupportComponents
open CanonicalIndex ConnectedBlocks
open scoped BigOperators
open DeletionCode.CatalogueFamily.PresentedFamily
variable {t k R : ℕ} {G : Fin R → Gram (windowLength k) → ℤ}
namespace DeletionCode.CatalogueFamily.PresentedFamily
theorem _root_.solution (P : PresentedFamily t k R G)
    (b : Fin (2 * t * R)) (v : Vertex (windowLength k))
    (hv : Incident (Finset.univ.image G) v)
    (hhas : HasVertex P.E.family (windowLength k) b v) :
    P.bubbleComponent b = Quotient.mk (ruleSetSetoid (Finset.univ.image G)) ⟨v, hv⟩ := by
  apply Quotient.sound
  change RuleSetConnected (Finset.univ.image G) (representative P.E.family (windowLength k) b) v
  rw [← P.rule_set]
  apply (rulesOfFamily_connected_iff P.E (CanonicalIndex.group t R)
    P.rank P.geometry P.disjoint _ _).mpr
  obtain ⟨side, i, hi, hv⟩ := hhas
  rw [hv]
  exact representative_connected P.E.family (windowLength k) P.common_start b side i hi
end DeletionCode.CatalogueFamily.PresentedFamily
