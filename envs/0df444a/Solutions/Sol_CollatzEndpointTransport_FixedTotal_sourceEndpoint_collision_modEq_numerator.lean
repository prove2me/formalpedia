-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sourceEndpoint_collision_modEq_numerator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:32:48.888807+00:00
-- url     : https://prove2.me/submissions/7c2ad029-c088-4fac-8e7b-252c21b35179

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalSourceCoding
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpoint_collision_modEq_correction
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
attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {M s : ℕ} (u : Fin M)
    (c d : Composition (M - (u : ℕ)))
    (hc : c.length = s) (hd : d.length = s)
    (hout :
      sourceEndpoint
          (Sum.inr ⟨u, c⟩ : SourceCode M) =
        sourceEndpoint
          (Sum.inr ⟨u, d⟩ : SourceCode M)) :
    Nat.ModEq (3 ^ s) (syracuseNumerator c)
      (syracuseNumerator d) := by
  have hcorr :
      Nat.ModEq (3 ^ s)
        (2 ^ (u : ℕ) * syracuseNumerator c)
        (2 ^ (u : ℕ) * syracuseNumerator d) := by
    simpa [sourceCodeOddCount, sourceCodeCorrection] using
      sourceEndpoint_collision_modEq_correction
        (M := M) (s := s)
        (x := (Sum.inr ⟨u, c⟩ : SourceCode M))
        (y := (Sum.inr ⟨u, d⟩ : SourceCode M))
        hc hd hout
  apply Nat.ModEq.cancel_left_of_coprime
  · exact
      (Nat.Coprime.pow s (u : ℕ)
        (by norm_num : Nat.Coprime 3 2)).gcd_eq_one
  · exact hcorr
end CollatzEndpointTransport.FixedTotal
