-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sourceEndpoint_lt_two_mul_three_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:59:38.87608+00:00
-- url     : https://prove2.me/submissions/55adc5bd-f023-4ae0-b1ac-f043df16a13d

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalSourceCoding
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpoint_eq_three_pow_add_residueEndpoint
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceResidueEndpoint_lt_three_pow

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {M s : ℕ} {x : SourceCode M}
    (hs : sourceCodeOddCount x = s) :
    sourceEndpoint x < 2 * 3 ^ s := by
  rw [sourceEndpoint_eq_three_pow_add_residueEndpoint, hs]
  have hres := sourceResidueEndpoint_lt_three_pow (x := x) hs
  omega
end CollatzEndpointTransport.FixedTotal
