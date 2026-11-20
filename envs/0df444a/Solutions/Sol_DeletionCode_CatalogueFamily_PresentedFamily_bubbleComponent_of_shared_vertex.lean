-- Prove2me | solution 1 for DeletionCode.CatalogueFamily.PresentedFamily.bubbleComponent_of_shared_vertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:24:41.470897+00:00
-- url     : https://prove2.me/submissions/a5c69b9e-a9cc-4d69-b509-f26b7b23c61f

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_CanonicalIndex
import Definitions.Def_DeletionCode_CatalogueFamily
import Theorems.Thm_DeletionCode_CatalogueFamily_PresentedFamily_bubbleComponent_vertex
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm


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
    (a b : Fin (2 * t * R)) (v : Vertex (windowLength k))
    (ha : HasVertex P.E.family (windowLength k) a v)
    (hb : HasVertex P.E.family (windowLength k) b v) :
    P.bubbleComponent a = P.bubbleComponent b := by
  have hv := P.incident_of_hasVertex a v ha
  exact (P.bubbleComponent_vertex a v hv ha).trans (P.bubbleComponent_vertex b v hv hb).symm
end DeletionCode.CatalogueFamily.PresentedFamily
