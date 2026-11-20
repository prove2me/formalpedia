-- Prove2me | solution 1 for DeletionCode.RelationSavings.savings_from_relation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:34:33.497467+00:00
-- url     : https://prove2.me/submissions/c5373e2f-5afc-4199-9e42-b3157a6bbc90

import Definitions.Def_DeletionCode_CatalogueFamily
import Definitions.Def_DeletionCode_ComponentFibers
import Definitions.Def_DeletionCode_RelationSupport
import Definitions.Def_DeletionCode_SupportInclusion
import Definitions.Def_DeletionCode_RelationSavings
import Theorems.Thm_DeletionCode_RelationSavings_savings_indexed
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm
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
theorem _root_.solution (I : RuleSet k)
    (hcat : ∀ u ∈ I, CatalogueRule t k u)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (a : (Gram (windowLength k) → ℤ) → ℚ)
    (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ)) :
    componentCount I ≤ t * I.card + t := by
  classical
  let e : Fin I.card ≃ I := by
    simpa only [Fintype.card_coe] using (Fintype.equivFin I).symm
  let G : Fin I.card → Gram (windowLength k) → ℤ := fun r => (e r).val
  have himage : Finset.univ.image G = I := by
    ext u
    constructor
    · intro hu
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hu
      exact (e r).property
    · intro hu
      obtain ⟨r, hr⟩ := e.surjective ⟨u, hu⟩
      exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, congrArg Subtype.val hr⟩
  have hre : RelationSupport.Relation G w (fun r => a (G r)) := by
    intro g
    rw [hrel g]
    have he := Equiv.sum_comp e (fun u : I => a u.val * (u.val g : ℚ))
    change (∑ u ∈ I, a u * (u g : ℚ)) =
      ∑ r, a (e r).val * ((e r).val g : ℚ)
    rw [he]
    exact (Finset.sum_coe_sort I (fun u => a u * (u g : ℚ))).symm
  have h := savings_indexed G (fun r => hcat _ (e r).property) w hw
    (fun r => a (G r)) (fun r => ha _ (e r).property) hre
  simpa only [himage] using h
end DeletionCode.RelationSavings
