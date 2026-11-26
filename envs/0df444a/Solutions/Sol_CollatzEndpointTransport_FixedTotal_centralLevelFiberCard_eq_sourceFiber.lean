-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralLevelFiberCard_eq_sourceFiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:37:43.549584+00:00
-- url     : https://prove2.me/submissions/d02492b1-82f4-4f75-8191-ca72d66f453d

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelSourceSet_eq_pairImage
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mixedFiberCard_eq_sigmaFiber
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
    (M s : ℕ) (theta eta : ℝ) (y : ℕ) :
    centralLevelFiberCard M s theta eta y =
      (mapFiber (centralLevelSourceSet M s theta eta)
        sourceEndpoint y).card := by
  classical
  let P := (Finset.univ : Finset (Fin M)).sigma
    (centralLevelCohortSet M s theta eta)
  let e : (Σ u : Fin M, Composition (M - (u : ℕ))) → SourceCode M :=
    fun p => Sum.inr p
  have hsource : centralLevelSourceSet M s theta eta = P.image e := by
    simpa [P, e, centralLevelPairImage] using
      centralLevelSourceSet_eq_pairImage M s theta eta
  rw [hsource]
  have hfilterImage :
      mapFiber (P.image e) sourceEndpoint y =
        (mapFiber P (fun p => cohortEndpoint p.1 p.2) y).image e := by
    ext x
    constructor
    · intro hx
      rw [mapFiber, Finset.mem_filter] at hx
      rcases Finset.mem_image.mp hx.1 with ⟨p, hp, rfl⟩
      rw [Finset.mem_image]
      refine ⟨p, ?_, rfl⟩
      rw [mapFiber, Finset.mem_filter]
      exact ⟨hp, by simpa [e, cohortEndpoint] using hx.2⟩
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
      rw [mapFiber, Finset.mem_filter] at hp ⊢
      exact ⟨Finset.mem_image.mpr ⟨p, hp.1, rfl⟩,
        by simpa [e, cohortEndpoint] using hp.2⟩
  rw [hfilterImage, Finset.card_image_of_injective _]
  · dsimp [centralLevelFiberCard, P]
    exact mixedFiberCard_eq_sigmaFiber
      (Finset.univ : Finset (Fin M))
      (centralLevelCohortSet M s theta eta)
      (fun u => cohortEndpoint u) y
  · intro p q hpq
    exact Sum.inr.inj hpq
end CollatzEndpointTransport.FixedTotal
