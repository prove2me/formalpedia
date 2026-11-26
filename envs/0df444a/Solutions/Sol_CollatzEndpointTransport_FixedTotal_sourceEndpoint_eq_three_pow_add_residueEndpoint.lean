-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sourceEndpoint_eq_three_pow_add_residueEndpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:32:16.252921+00:00
-- url     : https://prove2.me/submissions/340f982c-12a4-4525-8efe-a6357da5fdb7

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalSourceCoding
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpoint_affine
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceResidueEndpoint_affine

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {M : ℕ} (x : SourceCode M) :
    sourceEndpoint x =
      3 ^ sourceCodeOddCount x + sourceResidueEndpoint x := by
  have hshell := sourceEndpoint_affine x
  have hresidue := sourceResidueEndpoint_affine x
  have hmul :
      2 ^ M * sourceEndpoint x =
        2 ^ M *
          (3 ^ sourceCodeOddCount x + sourceResidueEndpoint x) := by
    calc
      2 ^ M * sourceEndpoint x =
          3 ^ sourceCodeOddCount x * sourceShellStart x +
            sourceCodeCorrection x := hshell
      _ = 3 ^ sourceCodeOddCount x *
              (2 ^ M + (sourceCodeEquivResidue M x : ℕ)) +
            sourceCodeCorrection x := by rw [sourceShellStart]
      _ = 3 ^ sourceCodeOddCount x * 2 ^ M +
            (3 ^ sourceCodeOddCount x *
                (sourceCodeEquivResidue M x : ℕ) +
              sourceCodeCorrection x) := by ring
      _ = 3 ^ sourceCodeOddCount x * 2 ^ M +
            2 ^ M * sourceResidueEndpoint x := by rw [hresidue]
      _ = 2 ^ M *
            (3 ^ sourceCodeOddCount x + sourceResidueEndpoint x) := by ring
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) M) hmul
end CollatzEndpointTransport.FixedTotal
