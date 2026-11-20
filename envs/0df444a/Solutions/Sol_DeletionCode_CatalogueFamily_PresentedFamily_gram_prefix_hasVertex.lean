-- Prove2me | solution 1 for DeletionCode.CatalogueFamily.PresentedFamily.gram_prefix_hasVertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:22:31.489832+00:00
-- url     : https://prove2.me/submissions/a4db366a-c246-41b2-8496-da39ecdf0b1f

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_CanonicalIndex
import Definitions.Def_DeletionCode_CatalogueFamily
import Theorems.Thm_DeletionCode_SignedSupport_prefix_gram


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
    (hg : HasGram P.E.family (windowLength k) b g) :
    HasVertex P.E.family (windowLength k) b (gramPrefix g) := by
  obtain ⟨side, i, hi⟩ := hg
  refine ⟨side, i.val, by have := i.isLt; omega, ?_⟩
  rw [← hi]
  exact prefix_gram P.E.family (windowLength k) b side i.val
end DeletionCode.CatalogueFamily.PresentedFamily
