-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.shellBad_collatzPullback_eq_endpointShellBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:27:46.218147+00:00
-- url     : https://prove2.me/submissions/51449e44-a244-4fe0-9966-9d818d51cae0

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalGlobalEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrectionDensity
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativePullbackDefs
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalShellCoding
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
import Theorems.Thm_CollatzEndpointTransport_Terras_log_two_eq_of_mem_dyadicShell
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
    QuantitativeDensity.shellBad
        (QuantitativeDensity.collatzPullback S) M =
      endpointShellBad S M := by
  classical
  ext n
  constructor
  · intro hn
    rw [QuantitativeDensity.shellBad, Finset.mem_filter] at hn
    simp only [endpointShellBad, Finset.mem_filter]
    have hlog :=
      Terras.log_two_eq_of_mem_dyadicShell hn.1
    exact
      ⟨hn.1, by
        simpa [QuantitativeDensity.collatzPullback, hlog] using hn.2⟩
  · intro hn
    simp only [endpointShellBad, Finset.mem_filter] at hn
    rw [QuantitativeDensity.shellBad, Finset.mem_filter]
    have hlog :=
      Terras.log_two_eq_of_mem_dyadicShell hn.1
    exact
      ⟨hn.1, by
        simpa [QuantitativeDensity.collatzPullback, hlog] using hn.2⟩
end CollatzEndpointTransport.FixedTotal
