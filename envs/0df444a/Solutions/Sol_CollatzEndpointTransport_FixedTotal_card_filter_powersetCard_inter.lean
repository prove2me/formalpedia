-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.card_filter_powersetCard_inter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:50:19.232447+00:00
-- url     : https://prove2.me/submissions/3788b1e0-55ca-4108-8cdf-4655e3ba30cb

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Factorial.BigOperators
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
variable {α : Type*} [DecidableEq α]
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (V U : Finset α) {k j : ℕ}
    (hUV : U ⊆ V) (hjk : j ≤ k) :
    ((V.powersetCard k).filter fun S => (U ∩ S).card = j).card =
      U.card.choose j * (V.card - U.card).choose (k - j) := by
  classical
  let source :=
    (V.powersetCard k).filter fun S => (U ∩ S).card = j
  let target :=
    (U.powersetCard j).product ((V \ U).powersetCard (k - j))
  have hcard :
      source.card = target.card := by
    refine Finset.card_bij'
      (fun S _ => (U ∩ S, S \ U))
      (fun AB _ => AB.1 ∪ AB.2) ?_ ?_ ?_ ?_
    · intro S hS
      have hSmem := Finset.mem_filter.mp hS
      have hSV := (Finset.mem_powersetCard.mp hSmem.1).1
      have hScard := (Finset.mem_powersetCard.mp hSmem.1).2
      apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_powersetCard.mpr
          ⟨Finset.inter_subset_left, hSmem.2⟩
      · apply Finset.mem_powersetCard.mpr
        constructor
        · intro x hx
          have hx' := Finset.mem_sdiff.mp hx
          exact Finset.mem_sdiff.mpr ⟨hSV hx'.1, hx'.2⟩
        · have hsplit := Finset.card_sdiff_add_card_inter S U
          rw [hScard, show (S ∩ U).card = (U ∩ S).card by
            rw [Finset.inter_comm], hSmem.2] at hsplit
          exact eq_tsub_of_add_eq hsplit
    · intro AB hAB
      have hA := (Finset.mem_product.mp hAB).1
      have hB := (Finset.mem_product.mp hAB).2
      have hAU := (Finset.mem_powersetCard.mp hA).1
      have hAcard := (Finset.mem_powersetCard.mp hA).2
      have hBVdiff := (Finset.mem_powersetCard.mp hB).1
      have hBcard := (Finset.mem_powersetCard.mp hB).2
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_powersetCard.mpr
        constructor
        · exact Finset.union_subset (hAU.trans hUV)
            (hBVdiff.trans Finset.sdiff_subset)
        · have hdisj : Disjoint AB.1 AB.2 := by
            refine Finset.disjoint_left.mpr ?_
            intro x hxA hxB
            have hxU := hAU hxA
            have hxNotU := (Finset.mem_sdiff.mp (hBVdiff hxB)).2
            exact hxNotU hxU
          rw [Finset.card_union_of_disjoint hdisj, hAcard, hBcard,
            Nat.add_sub_of_le hjk]
      · have hinter : U ∩ (AB.1 ∪ AB.2) = AB.1 := by
          ext x
          simp only [Finset.mem_inter, Finset.mem_union]
          constructor
          · rintro ⟨hxU, hxA | hxB⟩
            · exact hxA
            · exact False.elim
                ((Finset.mem_sdiff.mp (hBVdiff hxB)).2 hxU)
          · intro hxA
            exact ⟨hAU hxA, Or.inl hxA⟩
        rw [hinter, hAcard]
    · intro S hS
      ext x
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · rintro (⟨hxU, hxS⟩ | ⟨hxS, hxNotU⟩) <;> exact hxS
      · intro hxS
        by_cases hxU : x ∈ U
        · exact Or.inl ⟨hxU, hxS⟩
        · exact Or.inr ⟨hxS, hxU⟩
    · intro AB hAB
      have hA := (Finset.mem_product.mp hAB).1
      have hB := (Finset.mem_product.mp hAB).2
      have hAU := (Finset.mem_powersetCard.mp hA).1
      have hBVdiff := (Finset.mem_powersetCard.mp hB).1
      apply Prod.ext
      · ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hxU, hxA | hxB⟩
          · exact hxA
          · exact False.elim
              ((Finset.mem_sdiff.mp (hBVdiff hxB)).2 hxU)
        · intro hxA
          exact ⟨hAU hxA, Or.inl hxA⟩
      · ext x
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hxA | hxB, hxNotU⟩
          · exact False.elim (hxNotU (hAU hxA))
          · exact hxB
        · intro hxB
          exact ⟨Or.inr hxB, (Finset.mem_sdiff.mp (hBVdiff hxB)).2⟩
  calc
    ((V.powersetCard k).filter fun S => (U ∩ S).card = j).card =
        source.card := rfl
    _ = target.card := hcard
    _ = U.card.choose j * (V.card - U.card).choose (k - j) := by
      simp [target, Finset.card_sdiff_of_subset hUV]
end CollatzEndpointTransport.FixedTotal
