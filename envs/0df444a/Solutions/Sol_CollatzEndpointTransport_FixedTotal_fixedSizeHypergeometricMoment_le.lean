-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedSizeHypergeometricMoment_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:42:36.412187+00:00
-- url     : https://prove2.me/submissions/65d3b8c6-65e6-4200-81d9-1dc78dab9496

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Factorial.BigOperators
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_average_fixedSize_subsetMoment_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_filter_powersetCard_inter
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
    (V U : Finset α) {k : ℕ} {t : ℝ}
    (hUV : U ⊆ V) (hkV : k ≤ V.card) (hV : V.Nonempty)
    (ht : 0 ≤ t) :
    (∑ j ∈ range (U.card + 1),
        if hjk : j ≤ k then
          (U.card.choose j : ℝ) *
            ((V.card - U.card).choose (k - j) : ℝ) *
              (1 + t) ^ j
        else 0) / (V.card.choose k : ℝ) ≤
      (1 + ((k : ℝ) / V.card) * t) ^ U.card := by
  classical
  let Ω := V.powersetCard k
  have hmap :
      ∀ S ∈ Ω, (U ∩ S).card ∈ range (U.card + 1) := by
    intro S hS
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Finset.card_le_card Finset.inter_subset_left))
  have hpartition :
      (∑ j ∈ range (U.card + 1),
          ∑ S ∈ Ω with (U ∩ S).card = j,
            (1 + t) ^ (U ∩ S).card) =
        ∑ S ∈ Ω, (1 + t) ^ (U ∩ S).card := by
    simpa using
      (Finset.sum_fiberwise_of_maps_to
        (s := Ω) (t := range (U.card + 1))
        (g := fun S : Finset α => (U ∩ S).card)
        hmap (fun S => (1 + t) ^ (U ∩ S).card))
  have hgroup :
      (∑ j ∈ range (U.card + 1),
          if hjk : j ≤ k then
            (U.card.choose j : ℝ) *
              ((V.card - U.card).choose (k - j) : ℝ) *
                (1 + t) ^ j
          else 0) =
        ∑ S ∈ Ω, (1 + t) ^ (U ∩ S).card := by
    rw [← hpartition]
    apply sum_congr rfl
    intro j hj
    by_cases hjk : j ≤ k
    · rw [dif_pos hjk]
      have hcardNat :=
        card_filter_powersetCard_inter V U hUV hjk
      have hcardReal :
          (((V.powersetCard k).filter fun S =>
              (U ∩ S).card = j).card : ℝ) =
            (U.card.choose j : ℝ) *
              ((V.card - U.card).choose (k - j) : ℝ) := by
        exact_mod_cast hcardNat
      rw [← hcardReal]
      simp only [Ω]
      rw [show
          (∑ S ∈ V.powersetCard k with (U ∩ S).card = j,
              (1 + t) ^ (U ∩ S).card) =
            (((V.powersetCard k).filter fun S => (U ∩ S).card = j).card : ℝ) *
              (1 + t) ^ j by
        calc
          (∑ S ∈ V.powersetCard k with (U ∩ S).card = j,
              (1 + t) ^ (U ∩ S).card) =
              ∑ _S ∈
                (V.powersetCard k).filter (fun S => (U ∩ S).card = j),
                (1 + t) ^ j := by
                  apply Finset.sum_congr rfl
                  intro S hS
                  rw [(Finset.mem_filter.mp hS).2]
          _ = (((V.powersetCard k).filter fun S =>
                (U ∩ S).card = j).card : ℝ) * (1 + t) ^ j := by
                  simp]
    · rw [dif_neg hjk]
      have hempty :
          (V.powersetCard k).filter (fun S => (U ∩ S).card = j) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro S hS hEq
        have hScard := (Finset.mem_powersetCard.mp hS).2
        have hle : (U ∩ S).card ≤ S.card :=
          Finset.card_le_card Finset.inter_subset_right
        exact hjk (by simpa [hScard, hEq] using hle)
      rw [show
          (∑ S ∈ V.powersetCard k with (U ∩ S).card = j,
              (1 + t) ^ (U ∩ S).card) = 0 by
        rw [show
          (V.powersetCard k).filter (fun S => (U ∩ S).card = j) = ∅ from hempty]
        simp]
  rw [hgroup]
  exact average_fixedSize_subsetMoment_le V U hUV hkV hV ht
end CollatzEndpointTransport.FixedTotal
