-- Prove2me | solution 1 for DeletionCode.RelationSavings.singleton_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:26:42.907179+00:00
-- url     : https://prove2.me/submissions/57ebab4b-7269-4bb0-b47f-95c3d04d76d0

import Definitions.Def_DeletionCode_CatalogueFamily
import Definitions.Def_DeletionCode_ComponentFibers
import Definitions.Def_DeletionCode_RelationSupport
import Definitions.Def_DeletionCode_SupportInclusion
import Definitions.Def_DeletionCode_RelationSavings
import Theorems.Thm_DeletionCode_CatalogueBridge_ValidCatalogue_geometry
import Theorems.Thm_DeletionCode_CatalogueFamily_PresentedFamily_bubbleComponent_gram_prefix
import Theorems.Thm_DeletionCode_CatalogueFamily_PresentedFamily_bubbleComponent_of_common_gram
import Theorems.Thm_DeletionCode_CatalogueFamily_PresentedFamily_gram_prefix_hasVertex
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm
import Theorems.Thm_DeletionCode_SignedSupport_rule_negative_of_window
import Theorems.Thm_DeletionCode_SignedSupport_rule_support_iff
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
attribute [local simp] DeletionCode.ComponentFibers.mem_fiber
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk


section
namespace DeletionCode.RelationSavings
open HeaderRecovery SignedSupport RuleReconstruction RuleSetGraph SupportComponents
open SignedRuleCount ConnectedBlocks CatalogueFamily ComponentFibers SupportInclusion
open scoped BigOperators
variable {t k R : ℕ} {G : Fin R → Gram (windowLength k) → ℤ}
private theorem group_disjoint (P : PresentedFamily t k R G) (r : Fin R) :
    VertexDisjointOn P.E.family (windowLength k)
      (groupBubbles (CanonicalIndex.group t R) r) := by
  rw [← rank_bubbles_eq_group P.E (CanonicalIndex.group t R) P.rank r]
  exact P.disjoint r.val
end DeletionCode.RelationSavings
end

set_option autoImplicit true
open DeletionCode DeletionCode.RelationSavings
open HeaderRecovery SignedSupport RuleReconstruction RuleSetGraph SupportComponents
open SignedRuleCount ConnectedBlocks CatalogueFamily ComponentFibers SupportInclusion
open scoped BigOperators
variable {t k R : ℕ} {G : Fin R → Gram (windowLength k) → ℤ}
namespace DeletionCode.RelationSavings
theorem _root_.solution (P : PresentedFamily t k R G)
    (C : RuleSetComponents (Finset.univ.image G))
    (hC : SingletonFiber P.bubbleComponent C) :
    ∃ r g, G r g ≠ 0 ∧ (∀ s, s ≠ r → G s g = 0) ∧
      ∃ hg : Incident (Finset.univ.image G) (gramPrefix g),
        Quotient.mk (ruleSetSetoid (Finset.univ.image G)) ⟨gramPrefix g, hg⟩ = C := by
  classical
  obtain ⟨b, hb, huniq⟩ := hC
  let r := CanonicalIndex.group t R b
  let g := gram (P.E.family.path b false) (windowLength k) 0
  have hgram : g ∈ windowSet (P.E.family.path b false) (windowLength k)
      (P.E.family.extra b false) := ⟨⟨0, by omega⟩, rfl⟩
  have hhas : HasGram P.E.family (windowLength k) b g := ⟨false, hgram⟩
  have hmem : b ∈ groupBubbles (CanonicalIndex.group t R) r := by
    simp [groupBubbles, r]
  have hneg : G r g = -1 := by
    rw [← P.rule_eq r]
    exact rule_negative_of_window P.E.family (windowLength k) P.geometry _
      (group_disjoint P r) b hmem g hgram
  refine ⟨r, g, by omega, ?_, ?_⟩
  · intro s hsr
    by_contra hnonzero
    rw [← P.rule_eq s] at hnonzero
    obtain ⟨d, hd, hdg⟩ := (rule_support_iff P.E.family (windowLength k)
      P.geometry _ (group_disjoint P s) g).mp hnonzero
    have hdc : P.bubbleComponent d = C :=
      (P.bubbleComponent_of_common_gram d b g hdg hhas).trans hb
    have hdb := huniq d hdc
    have howner : CanonicalIndex.group t R d = s := (Finset.mem_filter.mp hd).2
    exact hsr (howner.symm.trans (congrArg (CanonicalIndex.group t R) hdb))
  · let hv := P.incident_of_hasVertex b _ (P.gram_prefix_hasVertex b g hhas)
    exact ⟨hv, (P.bubbleComponent_gram_prefix b g hhas hv).symm.trans hb⟩
end DeletionCode.RelationSavings
