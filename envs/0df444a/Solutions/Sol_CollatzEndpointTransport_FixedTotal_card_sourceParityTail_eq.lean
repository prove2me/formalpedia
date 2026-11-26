-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.card_sourceParityTail_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:32:54.038951+00:00
-- url     : https://prove2.me/submissions/a836f0b5-1d87-491a-908b-fdc145f9d163

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_centralSourceSet_inr
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_centralSourceSet_inl
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_sourceLateFirstOdd_inl
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_sourceLateFirstOdd_inr
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalizedReverseLift_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_oddCount_sourceShellStart
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceCodeEquivDyadicShell_val
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
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.card_positivePrefix
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.mem_basePullback
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.mem_collatzPullback
attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero


attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_centralSourceSet_inr
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_centralSourceSet_inl
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_sourceLateFirstOdd_inl
attribute [local simp] CollatzEndpointTransport.FixedTotal.mem_sourceLateFirstOdd_inr

set_option autoImplicit false
set_option maxHeartbeats 4000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (M : ℕ) (t : ℝ) :
    (sourceParityTail M t).card =
      (Terras.shellParityPrefixBadAt M M t).card := by
  classical
  apply Finset.card_bij (fun x _ => sourceShellStart x)
  · intro x hx
    rw [sourceParityTail, Finset.mem_filter] at hx
    rw [Terras.shellParityPrefixBadAt, Finset.mem_union]
    rcases hx.2 with hl | hu
    · left
      rw [Terras.shellLowerPrefixBad, Finset.mem_filter]
      exact ⟨by simpa [QuantitativeDensity.dyadicShell] using
        sourceShellStart_mem x, by simpa [oddCount_sourceShellStart] using hl⟩
    · right
      rw [Terras.shellUpperPrefixBad, Finset.mem_filter]
      exact ⟨by simpa [QuantitativeDensity.dyadicShell] using
        sourceShellStart_mem x, by simpa [oddCount_sourceShellStart] using hu⟩
  · intro x hx y hy hxy
    have heq :
        sourceCodeEquivDyadicShell M x = sourceCodeEquivDyadicShell M y := by
      apply Subtype.ext
      simpa [sourceCodeEquivDyadicShell_val] using hxy
    exact (sourceCodeEquivDyadicShell M).injective heq
  · intro n hn
    have hnShell : n ∈ QuantitativeDensity.dyadicShell M := by
      rw [Terras.shellParityPrefixBadAt, Finset.mem_union] at hn
      rcases hn with hn | hn
      · exact (Finset.mem_filter.mp hn).1
      · exact (Finset.mem_filter.mp hn).1
    let x : SourceCode M :=
      (sourceCodeEquivDyadicShell M).symm ⟨n, hnShell⟩
    have hxStart : sourceShellStart x = n := by
      have happly := (sourceCodeEquivDyadicShell M).apply_symm_apply
        ⟨n, hnShell⟩
      exact congrArg Subtype.val happly
    refine ⟨x, ?_, hxStart⟩
    rw [sourceParityTail, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Terras.shellParityPrefixBadAt, Finset.mem_union] at hn
    rcases hn with hn | hn
    · left
      have hodd := (Finset.mem_filter.mp hn).2
      simpa [← oddCount_sourceShellStart x, hxStart] using hodd
    · right
      have hodd := (Finset.mem_filter.mp hn).2
      simpa [← oddCount_sourceShellStart x, hxStart] using hodd
end CollatzEndpointTransport.FixedTotal
