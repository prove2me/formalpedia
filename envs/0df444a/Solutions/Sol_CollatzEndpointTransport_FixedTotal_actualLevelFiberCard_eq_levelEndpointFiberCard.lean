-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.actualLevelFiberCard_eq_levelEndpointFiberCard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:28:24.825793+00:00
-- url     : https://prove2.me/submissions/6afac25d-77e3-4d2b-9989-3955b5b9fba7

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalOddCountMGF
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
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
    {M s y : ℕ} (hs : 0 < s) :
    actualLevelFiberCard M s y =
      levelEndpointFiberCard M s y := by
  classical
  unfold actualLevelFiberCard mapFiber levelEndpointFiberCard mixedFiberCard
    levelCohortSet cohortEndpoint
  rw [sourceOddLevel, Finset.card_filter, Finset.sum_filter]
  rw [Fintype.sum_sum_type]
  simp only [sourceCodeOddCount, hs.ne'.symm, ↓reduceIte,
    Finset.sum_const_zero, zero_add]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro u hu
  unfold mapFiber
  rw [Finset.card_filter]
  simp only [fixedSet, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hlen : c.length = s <;> simp [hlen]
end CollatzEndpointTransport.FixedTotal
