-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.card_sourceEndpointBad_eq_endpointShellBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:27:01.513718+00:00
-- url     : https://prove2.me/submissions/3be0c57a-9b68-42db-bcc0-49bcad2bda73

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalGlobalEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrectionDensity
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativePullbackDefs
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalShellCoding
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceCodeEquivDyadicShell_val
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceShellStart_mem
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
    (sourceEndpointBad S M).card = (endpointShellBad S M).card := by
  classical
  apply Finset.card_bij
      (fun x _ => sourceShellStart x)
  · intro x hx
    simp only [endpointShellBad, Finset.mem_filter]
    exact
      ⟨by
        simpa [QuantitativeDensity.dyadicShell] using
          sourceShellStart_mem x,
        by
          simpa [sourceEndpoint] using
            (Finset.mem_filter.mp hx).2⟩
  · intro x hx y hy hxy
    have heq :
        sourceCodeEquivDyadicShell M x =
          sourceCodeEquivDyadicShell M y := by
      apply Subtype.ext
      simpa [sourceCodeEquivDyadicShell_val] using hxy
    exact (sourceCodeEquivDyadicShell M).injective heq
  · intro n hn
    have hnPair :
        n ∈ QuantitativeDensity.dyadicShell M ∧
          (Terras.T^[M]) n ∉ S := by
      simpa only [endpointShellBad, Finset.mem_filter] using hn
    have hnShell :
        n ∈ QuantitativeDensity.dyadicShell M :=
      hnPair.1
    let x : SourceCode M :=
      (sourceCodeEquivDyadicShell M).symm ⟨n, hnShell⟩
    refine ⟨x, ?_, ?_⟩
    · rw [sourceEndpointBad, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hx :
          sourceShellStart x = n := by
        have happly :=
          (sourceCodeEquivDyadicShell M).apply_symm_apply
            ⟨n, hnShell⟩
        exact congrArg Subtype.val happly
      simpa [sourceEndpoint, hx] using
        hnPair.2
    · have happly :=
        (sourceCodeEquivDyadicShell M).apply_symm_apply
          ⟨n, hnShell⟩
      exact congrArg Subtype.val happly
end CollatzEndpointTransport.FixedTotal
