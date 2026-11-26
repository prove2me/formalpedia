-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.card_sourceOddLevel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:29:44.624099+00:00
-- url     : https://prove2.me/submissions/dfcb1070-d34c-4b35-a849-dbadb8ae5142

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalShellCoding
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalOddCountMGF
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_oddCount_sourceCodeEquivResidue
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_nil
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_card_positivePrefix
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_basePullback
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_collatzPullback
import Theorems.Thm_CollatzEndpointTransport_Terras_card_residues_with_oddCount
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
    (M s : ℕ) :
    (sourceOddLevel M s).card = M.choose s := by
  classical
  have hcard :
      (sourceOddLevel M s).card =
        (Finset.univ.filter
          (fun r : Fin (2 ^ M) =>
            Terras.oddCount M (r : ℕ) = s)).card := by
    apply Finset.card_bij
        (fun x _ => sourceCodeEquivResidue M x)
    · intro x hx
      simp only [sourceOddLevel, Finset.mem_filter,
        Finset.mem_univ, true_and] at hx ⊢
      simpa [oddCount_sourceCodeEquivResidue] using hx
    · intro x hx y hy hxy
      exact (sourceCodeEquivResidue M).injective hxy
    · intro r hr
      let x : SourceCode M :=
        (sourceCodeEquivResidue M).symm r
      refine ⟨x, ?_, ?_⟩
      · rw [sourceOddLevel, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have happly :
            sourceCodeEquivResidue M x = r :=
          (sourceCodeEquivResidue M).apply_symm_apply r
        have hrOdd :=
          (Finset.mem_filter.mp hr).2
        rw [← oddCount_sourceCodeEquivResidue M x, happly]
        exact hrOdd
      · exact (sourceCodeEquivResidue M).apply_symm_apply r
  rw [hcard, Terras.card_residues_with_oddCount]
end CollatzEndpointTransport.FixedTotal
