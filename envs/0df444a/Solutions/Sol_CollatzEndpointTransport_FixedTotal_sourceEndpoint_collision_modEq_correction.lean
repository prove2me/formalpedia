-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sourceEndpoint_collision_modEq_correction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:31:13.894065+00:00
-- url     : https://prove2.me/submissions/9b9e17c0-6afc-44cf-8bd6-a2be006bdad2

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalSourceCoding
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_integerCorrection_sourceShellStart
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_oddCount_sourceShellStart
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
import Theorems.Thm_CollatzEndpointTransport_Terras_correction_modEq_of_equal_output
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
    {M s : ℕ} {x y : SourceCode M}
    (hsx : sourceCodeOddCount x = s)
    (hsy : sourceCodeOddCount y = s)
    (hout : sourceEndpoint x = sourceEndpoint y) :
    Nat.ModEq (3 ^ s) (sourceCodeCorrection x)
      (sourceCodeCorrection y) := by
  have h :=
    Terras.correction_modEq_of_equal_output
      (M := M) (s := s)
      (n₁ := sourceShellStart x) (n₂ := sourceShellStart y)
      (by simpa [oddCount_sourceShellStart] using hsx)
      (by simpa [oddCount_sourceShellStart] using hsy)
      (by simpa [sourceEndpoint] using hout)
  rw [integerCorrection_sourceShellStart,
    integerCorrection_sourceShellStart] at h
  exact h
end CollatzEndpointTransport.FixedTotal
