-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.actualLevelEndpointSet_eq_levelEndpointSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:28:29.980831+00:00
-- url     : https://prove2.me/submissions/07a85cc2-3895-4fda-a209-c4768143930d

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
    {M s : ℕ} (hs : 0 < s) :
    actualLevelEndpointSet M s = levelEndpointSet M s := by
  classical
  ext y
  constructor
  · intro hy
    rw [actualLevelEndpointSet, Finset.mem_image] at hy
    rcases hy with ⟨x, hx, rfl⟩
    have hsx : sourceCodeOddCount x = s :=
      (Finset.mem_filter.mp hx).2
    cases x with
    | inl e =>
        simp [sourceCodeOddCount] at hsx
        omega
    | inr p =>
        rcases p with ⟨u, c⟩
        rw [levelEndpointSet, mixedTargetSet, Finset.mem_biUnion]
        refine ⟨u, Finset.mem_univ _, ?_⟩
        rw [Finset.mem_image]
        refine ⟨c, ?_, rfl⟩
        rw [levelCohortSet, fixedSet, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by
          simpa [sourceCodeOddCount] using hsx⟩
  · intro hy
    rw [levelEndpointSet, mixedTargetSet, Finset.mem_biUnion] at hy
    rcases hy with ⟨u, hu, hyu⟩
    rw [Finset.mem_image] at hyu
    rcases hyu with ⟨c, hc, rfl⟩
    rw [actualLevelEndpointSet, Finset.mem_image]
    refine
      ⟨(Sum.inr ⟨u, c⟩ : SourceCode M), ?_, rfl⟩
    rw [sourceOddLevel, Finset.mem_filter]
    have hlen :
        c.length = s :=
      (Finset.mem_filter.mp hc).2
    exact ⟨Finset.mem_univ _, by
      simpa [sourceCodeOddCount] using hlen⟩
end CollatzEndpointTransport.FixedTotal
