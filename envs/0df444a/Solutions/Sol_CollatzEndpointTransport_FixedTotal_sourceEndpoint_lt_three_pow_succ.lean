-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sourceEndpoint_lt_three_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:32:47.196031+00:00
-- url     : https://prove2.me/submissions/1a77f116-ed49-4734-9c97-187b0aee8386

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalSourceCoding
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceShellStart_mem
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_integerCorrection_sourceShellStart
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_oddCount_sourceShellStart
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpoint_affine
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
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_lt_scale
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
    sourceEndpoint x < 3 ^ (s + 1) := by
  have haffine := sourceEndpoint_affine x
  rw [hs] at haffine
  have hstart := (sourceShellStart_mem x).2
  have hcorr :=
    Terras.integerCorrection_lt_scale M (sourceShellStart x)
  rw [integerCorrection_sourceShellStart,
    oddCount_sourceShellStart, hs] at hcorr
  have hpow2 : 0 < 2 ^ M := pow_pos (by norm_num) _
  have hthree : 0 < 3 ^ s := pow_pos (by norm_num) _
  have hstart' :
      sourceShellStart x < 2 ^ M * 2 := by
    simpa only [pow_succ] using hstart
  have hmain :
      3 ^ s * sourceShellStart x <
        3 ^ s * (2 ^ M * 2) :=
    (Nat.mul_lt_mul_left hthree).2 hstart'
  have hsum :
      3 ^ s * sourceShellStart x + sourceCodeCorrection x <
        3 ^ s * (2 ^ M * 2) + 3 ^ s * 2 ^ M :=
    Nat.add_lt_add hmain hcorr
  have hstrict :
      2 ^ M * sourceEndpoint x <
        2 ^ M * 3 ^ (s + 1) := by
    rw [haffine]
    calc
      3 ^ s * sourceShellStart x + sourceCodeCorrection x <
          3 ^ s * (2 ^ M * 2) + 3 ^ s * 2 ^ M := hsum
      _ = 2 ^ M * 3 ^ (s + 1) := by
        rw [pow_succ]
        ring
  exact (Nat.mul_lt_mul_left hpow2).mp <| by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hstrict
end CollatzEndpointTransport.FixedTotal
