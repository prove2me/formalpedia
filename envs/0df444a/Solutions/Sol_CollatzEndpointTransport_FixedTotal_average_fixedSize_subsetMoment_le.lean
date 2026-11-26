-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.average_fixedSize_subsetMoment_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:51:07.111798+00:00
-- url     : https://prove2.me/submissions/31763695-83de-4165-b79d-19f387c9e698

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Factorial.BigOperators
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_choose_sub_div_choose_le_pow_div
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_powerset_pow_card
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_subsetMomentExpansion
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
    (∑ S ∈ V.powersetCard k, (1 + t) ^ (U ∩ S).card) /
        (V.card.choose k : ℝ) ≤
      (1 + ((k : ℝ) / V.card) * t) ^ U.card := by
  classical
  let Ω := V.powersetCard k
  have hVcard : 0 < V.card := Finset.card_pos.mpr hV
  have hden : 0 < (V.card.choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos hkV
  have hsum :
      (∑ S ∈ Ω, (1 + t) ^ (U ∩ S).card) =
        ∑ J ∈ U.powerset,
          ((Ω.filter (J ⊆ ·)).card : ℝ) * t ^ J.card := by
    calc
      (∑ S ∈ Ω, (1 + t) ^ (U ∩ S).card) =
          ∑ S ∈ Ω,
            ∑ J ∈ U.powerset, if J ⊆ S then t ^ J.card else 0 := by
        apply sum_congr rfl
        intro S hS
        exact subsetMomentExpansion U S t
      _ = ∑ J ∈ U.powerset,
          ∑ S ∈ Ω, if J ⊆ S then t ^ J.card else 0 := by
        rw [sum_comm]
      _ = ∑ J ∈ U.powerset,
          ((Ω.filter (J ⊆ ·)).card : ℝ) * t ^ J.card := by
        apply sum_congr rfl
        intro J hJ
        rw [← Finset.sum_filter]
        simp
  rw [hsum, div_eq_mul_inv, Finset.sum_mul]
  calc
    (∑ J ∈ U.powerset,
        (((Ω.filter (J ⊆ ·)).card : ℝ) * t ^ J.card) *
          (V.card.choose k : ℝ)⁻¹) ≤
        ∑ J ∈ U.powerset,
          (((k : ℝ) / V.card) * t) ^ J.card := by
      apply sum_le_sum
      intro J hJ
      have hJU : J ⊆ U := Finset.mem_powerset.mp hJ
      have hJV : J ⊆ V := hJU.trans hUV
      by_cases hJk : J.card ≤ k
      · rw [show (Ω.filter (J ⊆ ·)).card =
            (V.card - J.card).choose (k - J.card) by
          exact Finset.card_filter_powersetCard_subset J V k hJV hJk]
        have hratio :=
          choose_sub_div_choose_le_pow_div hVcard hkV hJk
        calc
          ((((V.card - J.card).choose (k - J.card) : ℕ) : ℝ) *
                t ^ J.card) * (V.card.choose k : ℝ)⁻¹ =
            ((((V.card - J.card).choose (k - J.card) : ℕ) : ℝ) /
              (V.card.choose k : ℝ)) * t ^ J.card := by ring
          _ ≤ (((k : ℝ) / V.card) ^ J.card) * t ^ J.card :=
            mul_le_mul_of_nonneg_right hratio (pow_nonneg ht _)
          _ = (((k : ℝ) / V.card) * t) ^ J.card := by
            rw [mul_pow]
      · have hempty : Ω.filter (J ⊆ ·) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro S hSmem hJS
          have hScard : S.card = k :=
            (Finset.mem_powersetCard.mp hSmem).2
          exact hJk (by simpa [hScard] using Finset.card_le_card hJS)
        rw [hempty]
        simp
        positivity
    _ = (1 + ((k : ℝ) / V.card) * t) ^ U.card :=
      sum_powerset_pow_card U (((k : ℝ) / V.card) * t)
end CollatzEndpointTransport.FixedTotal
