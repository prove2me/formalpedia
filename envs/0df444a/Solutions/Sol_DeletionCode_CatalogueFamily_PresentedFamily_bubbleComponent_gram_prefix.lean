-- Prove2me | solution 1 for DeletionCode.CatalogueFamily.PresentedFamily.bubbleComponent_gram_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:24:41.899096+00:00
-- url     : https://prove2.me/submissions/bfc91ab8-77b6-44ab-b4de-cc368e7d358d

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_CanonicalIndex
import Definitions.Def_DeletionCode_CatalogueFamily
import Theorems.Thm_DeletionCode_CatalogueFamily_PresentedFamily_bubbleComponent_vertex
import Theorems.Thm_DeletionCode_CatalogueFamily_PresentedFamily_gram_prefix_hasVertex

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
    (b : Fin (2 * t * R)) (g : Gram (windowLength k))
    (hg : HasGram P.E.family (windowLength k) b g)
    (hv : Incident (Finset.univ.image G) (gramPrefix g)) :
    P.bubbleComponent b =
      Quotient.mk (ruleSetSetoid (Finset.univ.image G)) ⟨gramPrefix g, hv⟩ :=
  P.bubbleComponent_vertex b (gramPrefix g) hv (P.gram_prefix_hasVertex b g hg)
end DeletionCode.CatalogueFamily.PresentedFamily
