-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sourceEndpoint_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:32:43.073791+00:00
-- url     : https://prove2.me/submissions/9b7e287b-5bc0-44b0-9a2e-176d9d5ff652

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalSourceCoding
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceShellStart_mem
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpoint_affine

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {M : ℕ} (x : SourceCode M) :
    0 < sourceEndpoint x := by
  have haffine := sourceEndpoint_affine x
  have hstart : 0 < sourceShellStart x := by
    have hmem := (sourceShellStart_mem x).1
    have hpow : 0 < 2 ^ M := pow_pos (by norm_num) _
    omega
  have hrhs :
      0 <
        3 ^ sourceCodeOddCount x * sourceShellStart x +
          sourceCodeCorrection x := by
    positivity
  have hlhs : 0 < 2 ^ M * sourceEndpoint x := by
    rw [haffine]
    exact hrhs
  exact Nat.pos_of_mul_pos_left hlhs
end CollatzEndpointTransport.FixedTotal
