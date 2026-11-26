-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.card_sourceEndpointBad_eq_sum_levelBadMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:35:40.360532+00:00
-- url     : https://prove2.me/submissions/2396ad38-04be-4b6f-a4ab-ab0a18c88e0e

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointTarget
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_actualLevelBadMass_eq_card_filter
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceCodeOddCount_le
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
    (S : Set ℕ) (M : ℕ) :
    (sourceEndpointBad S M).card =
      ∑ s ∈ Finset.range (M + 1),
        actualLevelBadMass S M s := by
  classical
  have hmap :
      ∀ x ∈ (Finset.univ : Finset (SourceCode M)),
        sourceCodeOddCount x ∈ Finset.range (M + 1) := by
    intro x hx
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (sourceCodeOddCount_le x))
  calc
    (sourceEndpointBad S M).card =
        ∑ x : SourceCode M,
          if sourceEndpoint x ∉ S then 1 else 0 := by
      rw [sourceEndpointBad, Finset.card_filter]
    _ = ∑ s ∈ Finset.range (M + 1),
          ∑ x ∈ sourceOddLevel M s,
            if sourceEndpoint x ∉ S then 1 else 0 := by
      symm
      simpa [sourceOddLevel] using
        (Finset.sum_fiberwise_of_maps_to
          (s := (Finset.univ : Finset (SourceCode M)))
          (t := Finset.range (M + 1))
          (g := sourceCodeOddCount)
          hmap
          (fun x => if sourceEndpoint x ∉ S then 1 else 0))
    _ = ∑ s ∈ Finset.range (M + 1),
          actualLevelBadMass S M s := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [actualLevelBadMass_eq_card_filter]
      unfold sourceLevelBadSet
      rw [Finset.card_filter]
end CollatzEndpointTransport.FixedTotal
