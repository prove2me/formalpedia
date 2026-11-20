-- Prove2me | solution 1 for DeletionCode.RelationSavings.savings_indexed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:31:27.002715+00:00
-- url     : https://prove2.me/submissions/af46b582-ece6-42ab-874f-7171fd30011c

import Definitions.Def_DeletionCode_CatalogueFamily
import Definitions.Def_DeletionCode_ComponentFibers
import Definitions.Def_DeletionCode_RelationSupport
import Definitions.Def_DeletionCode_SupportInclusion
import Definitions.Def_DeletionCode_RelationSavings
import Theorems.Thm_DeletionCode_RelationSavings_singleton_hit
import Theorems.Thm_DeletionCode_CatalogueFamily_PresentedFamily_bubbleComponent_surjective
import Theorems.Thm_DeletionCode_ComponentFibers_component_count_bound
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_ConnectedBlocks_catalogue_singleton_component_count_le
import Theorems.Thm_DeletionCode_SupportInclusion_hit_component_count_le
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
attribute [local simp] DeletionCode.ComponentFibers.mem_fiber
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk



set_option autoImplicit true
open DeletionCode DeletionCode.RelationSavings
open HeaderRecovery SignedSupport RuleReconstruction RuleSetGraph SupportComponents
open SignedRuleCount ConnectedBlocks CatalogueFamily ComponentFibers SupportInclusion
open scoped BigOperators
variable {t k R : ℕ} {G : Fin R → Gram (windowLength k) → ℤ}
namespace DeletionCode.RelationSavings
theorem _root_.solution (G : Fin R → Gram (windowLength k) → ℤ)
    (hcat : ∀ r, CatalogueRule t k (G r))
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (a : Fin R → ℚ) (ha : ∀ r, a r ≠ 0)
    (hrel : RelationSupport.Relation G w a) :
    componentCount (Finset.univ.image G) ≤ t * R + t := by
  classical
  let P := ofCatalogue G hcat
  have hsingle : Fintype.card {C // SingletonFiber P.bubbleComponent C} ≤ 2 * t := by
    exact (hit_component_count_le (relation_support_included w a hrel)
      (SingletonFiber P.bubbleComponent) (singleton_hit P w a hrel ha)).trans
      (catalogue_singleton_component_count_le w hw)
  have hcount := component_count_bound P.bubbleComponent P.bubbleComponent_surjective t R
    (Fintype.card_fin _) hsingle
  simpa only [componentCount, Nat.card_eq_fintype_card] using hcount
end DeletionCode.RelationSavings
