-- Prove2me | solution 1 for DeletionCode.CatalogueFamily.PresentedFamily.bubbleComponent_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:24:40.955647+00:00
-- url     : https://prove2.me/submissions/deef65a3-b78c-417a-a59e-f1fbead22128

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_CanonicalIndex
import Definitions.Def_DeletionCode_CatalogueFamily
import Theorems.Thm_DeletionCode_CatalogueFamily_PresentedFamily_bubbleComponent_vertex
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
theorem _root_.solution (P : PresentedFamily t k R G) :
    Function.Surjective P.bubbleComponent := by
  intro C
  refine Quotient.inductionOn C ?_
  intro v
  have hv : ∃ b, HasVertex P.E.family (windowLength k) b v.val := by
    apply (incident_iff_supported P.E (CanonicalIndex.group t R)
      P.rank P.geometry P.disjoint v.val).mp
    simpa only [P.rule_set] using v.property
  obtain ⟨b, hb⟩ := hv
  exact ⟨b, P.bubbleComponent_vertex b v.val v.property hb⟩
end DeletionCode.CatalogueFamily.PresentedFamily
