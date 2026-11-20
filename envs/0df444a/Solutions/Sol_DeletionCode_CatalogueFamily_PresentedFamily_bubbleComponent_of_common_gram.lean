-- Prove2me | solution 1 for DeletionCode.CatalogueFamily.PresentedFamily.bubbleComponent_of_common_gram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:25:31.222465+00:00
-- url     : https://prove2.me/submissions/9c30737a-ef9a-4e8b-90e1-e2b900a87ed4

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_CanonicalIndex
import Definitions.Def_DeletionCode_CatalogueFamily
import Theorems.Thm_DeletionCode_CatalogueFamily_PresentedFamily_bubbleComponent_of_shared_vertex
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm
import Theorems.Thm_DeletionCode_SignedSupport_gram_eq_source_vertices


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
    (a b : Fin (2 * t * R)) (g : Gram (windowLength k))
    (ha : HasGram P.E.family (windowLength k) a g)
    (hb : HasGram P.E.family (windowLength k) b g) :
    P.bubbleComponent a = P.bubbleComponent b := by
  obtain ⟨sa, i, hi⟩ := ha
  obtain ⟨sb, j, hj⟩ := hb
  have hvertex := gram_eq_source_vertices P.E.family (windowLength k) a b sa sb i.val j.val
    (hi.trans hj.symm)
  apply P.bubbleComponent_of_shared_vertex a b (vertex P.E.family (windowLength k) a sa i.val)
  · exact ⟨sa, i.val, by have := i.isLt; omega, rfl⟩
  · exact ⟨sb, j.val, by have := j.isLt; omega, hvertex⟩
end DeletionCode.CatalogueFamily.PresentedFamily
