-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.actualLevelCriticalContribution_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:31:34.397226+00:00
-- url     : https://prove2.me/submissions/7fa02a41-1b13-4e74-8305-5d8895ab4f18

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalOddCountMGF
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_sourceOddLevel
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
    (M : ℕ) :
    actualLevelCriticalContribution M 0 = 1 := by
  classical
  have hcard : (sourceOddLevel M 0).card = 1 := by
    rw [card_sourceOddLevel]
    simp
  obtain ⟨x, hset⟩ := Finset.card_eq_one.mp hcard
  have hendpoint :
      actualLevelEndpointSet M 0 = {sourceEndpoint x} := by
    simp [actualLevelEndpointSet, hset]
  have hfiber :
      actualLevelFiberCard M 0 (sourceEndpoint x) = 1 := by
    rw [actualLevelFiberCard, mapFiber, hset]
    have hfilter :
        ({x} : Finset (SourceCode M)).filter
            (fun z => sourceEndpoint z = sourceEndpoint x) =
          {x} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · exact fun hz => hz.1
      · intro hz
        subst z
        exact ⟨rfl, rfl⟩
    rw [hfilter]
    simp
  simp [actualLevelCriticalContribution, hendpoint, hfiber, hcard]
end CollatzEndpointTransport.FixedTotal
