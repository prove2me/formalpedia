-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.actualLevelBadMass_eq_card_filter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:34:20.88349+00:00
-- url     : https://prove2.me/submissions/7e3a09b4-b19d-4047-bfa5-4c93f951b6e5

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointTarget
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_nil
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_card_positivePrefix
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_basePullback
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_collatzPullback
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_zero
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_nil
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.card_positivePrefix
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.mem_basePullback
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.mem_collatzPullback
attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (S : Set ℕ) (M s : ℕ) :
    actualLevelBadMass S M s =
      (sourceLevelBadSet S M s).card := by
  classical
  let W := sourceOddLevel M s
  let f : SourceCode M → ℕ := sourceEndpoint
  have hmaps :
      ∀ x ∈ W, f x ∈ actualLevelEndpointSet M s := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  calc
    actualLevelBadMass S M s =
        ∑ y ∈ actualLevelEndpointSet M s,
          ∑ x ∈ mapFiber W f y,
            if f x ∉ S then 1 else 0 := by
      unfold actualLevelBadMass
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hyS : y ∈ S
      · rw [if_neg (not_not.mpr hyS)]
        symm
        apply Finset.sum_eq_zero
        intro x hx
        have hfx : f x = y := (Finset.mem_filter.mp hx).2
        simp [hfx, hyS]
      · rw [if_pos hyS]
        calc
          actualLevelFiberCard M s y =
              (mapFiber W f y).card := rfl
          _ = ∑ _x ∈ mapFiber W f y, 1 := by simp
          _ = ∑ x ∈ mapFiber W f y,
                if f x ∉ S then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro x hx
            have hfx : f x = y := (Finset.mem_filter.mp hx).2
            simp [hfx, hyS]
    _ = ∑ x ∈ W, if f x ∉ S then 1 else 0 :=
      Finset.sum_fiberwise_of_maps_to hmaps
        (fun x => if f x ∉ S then 1 else 0)
    _ = (sourceLevelBadSet S M s).card := by
      unfold sourceLevelBadSet
      rw [Finset.card_filter]
end CollatzEndpointTransport.FixedTotal
