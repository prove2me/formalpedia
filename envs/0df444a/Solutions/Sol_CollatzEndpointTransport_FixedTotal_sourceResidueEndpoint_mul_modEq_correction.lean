-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sourceResidueEndpoint_mul_modEq_correction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:31:20.694354+00:00
-- url     : https://prove2.me/submissions/5fa8d23c-2295-43b6-ac0a-cc4e331abdc6

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalSourceCoding
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceResidueEndpoint_affine
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
    {M s : ℕ} {x : SourceCode M}
    (hs : sourceCodeOddCount x = s) :
    Nat.ModEq (3 ^ s)
      (2 ^ M * sourceResidueEndpoint x) (sourceCodeCorrection x) := by
  have h := sourceResidueEndpoint_affine x
  rw [hs] at h
  rw [Nat.ModEq]
  have hmod := congrArg (fun z : ℕ => z % 3 ^ s) h
  simpa [Nat.add_mod, Nat.mul_mod] using hmod
end CollatzEndpointTransport.FixedTotal
