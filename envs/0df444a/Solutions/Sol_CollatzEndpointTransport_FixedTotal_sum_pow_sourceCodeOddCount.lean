-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sum_pow_sourceCodeOddCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:31:31.275304+00:00
-- url     : https://prove2.me/submissions/bc2e213e-180a-4bfa-a65d-a378144e1dae

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalShellCoding
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalOddCountMGF
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceCodeOddCount_le
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
    (M : ℕ) (q : ℝ) :
    (∑ x : SourceCode M, q ^ sourceCodeOddCount x) =
      (1 + q) ^ M := by
  classical
  have hmap :
      ∀ x ∈ (Finset.univ : Finset (SourceCode M)),
        sourceCodeOddCount x ∈ Finset.range (M + 1) := by
    intro x hx
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (sourceCodeOddCount_le x))
  calc
    (∑ x : SourceCode M, q ^ sourceCodeOddCount x) =
        ∑ s ∈ Finset.range (M + 1),
          ∑ x ∈ sourceOddLevel M s,
            q ^ sourceCodeOddCount x := by
      symm
      simpa [sourceOddLevel] using
        (Finset.sum_fiberwise_of_maps_to
          (s := (Finset.univ : Finset (SourceCode M)))
          (t := Finset.range (M + 1))
          (g := sourceCodeOddCount)
          hmap
          (fun x => q ^ sourceCodeOddCount x))
    _ = ∑ s ∈ Finset.range (M + 1),
          (M.choose s : ℝ) * q ^ s := by
      apply Finset.sum_congr rfl
      intro s hs
      calc
        (∑ x ∈ sourceOddLevel M s,
            q ^ sourceCodeOddCount x) =
            ∑ _x ∈ sourceOddLevel M s, q ^ s := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [(Finset.mem_filter.mp hx).2]
        _ = (sourceOddLevel M s).card * q ^ s := by simp
        _ = (M.choose s : ℝ) * q ^ s := by
          rw [card_sourceOddLevel]
    _ = (q + 1) ^ M := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro s hs
      simp [mul_assoc, mul_left_comm, mul_comm]
    _ = (1 + q) ^ M := by ring
end CollatzEndpointTransport.FixedTotal
