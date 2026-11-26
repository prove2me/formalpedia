-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralLevelBadMass_eq_sum_bad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:39:33.818487+00:00
-- url     : https://prove2.me/submissions/ce5c5ecd-8330-4734-a159-bad5de3b04ab

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelFiberCard_eq_sourceFiber
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpoint_mem_centralLevelEndpointSet
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_centralSourceSet_inl
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_centralSourceSet_inr
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_sourceLateFirstOdd_inl
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_sourceLateFirstOdd_inr
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalizedReverseLift_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_nil
import Theorems.Thm_CollatzEndpointTransport_OptimizedLinearPullback_psi_zero
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_card_positivePrefix
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_basePullback
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_collatzPullback
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_zero
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_centralSourceSet_inl
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_centralSourceSet_inr
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_sourceLateFirstOdd_inl
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_sourceLateFirstOdd_inr
attribute [local simp] CollatzEndpointTransport.FixedTotal.normalizedReverseLift_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_nil
attribute [local simp] CollatzEndpointTransport.OptimizedLinearPullback.psi_zero
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.card_positivePrefix
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.mem_basePullback
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.mem_collatzPullback
attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real Topology
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralPullbackSourceCodeDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (S : Set ℕ) (M s : ℕ) (theta eta : ℝ) :
    centralLevelBadMass S M s theta eta =
      ∑ y ∈ centralLevelBadEndpointSet S M s theta eta,
        centralLevelFiberCard M s theta eta y := by
  classical
  let W := centralLevelSourceSet M s theta eta
  let f : SourceCode M → ℕ := sourceEndpoint
  have hmaps :
      ∀ x ∈ W, f x ∈ centralLevelEndpointSet M s theta eta := by
    exact fun x hx => sourceEndpoint_mem_centralLevelEndpointSet hx
  unfold centralLevelBadMass centralLevelBadEndpointSet
  rw [Finset.card_filter]
  rw [show
    (∑ x ∈ W, if f x ∉ S then 1 else 0) =
      ∑ y ∈ centralLevelEndpointSet M s theta eta,
        ∑ x ∈ mapFiber W f y,
          if f x ∉ S then 1 else 0 by
      symm
      exact Finset.sum_fiberwise_of_maps_to hmaps
        (fun x => if f x ∉ S then 1 else 0)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hyS : y ∈ S
  · rw [if_neg (not_not.mpr hyS)]
    apply Finset.sum_eq_zero
    intro x hx
    have hfx : f x = y := (Finset.mem_filter.mp hx).2
    rw [if_neg]
    simpa [hfx] using hyS
  · rw [if_pos hyS]
    calc
      ∑ x ∈ mapFiber W f y, (if f x ∉ S then 1 else 0) =
          ∑ _x ∈ mapFiber W f y, 1 := by
        apply Finset.sum_congr rfl
        intro x hx
        have hfx : f x = y := (Finset.mem_filter.mp hx).2
        simp [hfx, hyS]
      _ = (mapFiber W f y).card := by simp
      _ = centralLevelFiberCard M s theta eta y := by
        exact (centralLevelFiberCard_eq_sourceFiber M s theta eta y).symm
end CollatzEndpointTransport.FixedTotal
