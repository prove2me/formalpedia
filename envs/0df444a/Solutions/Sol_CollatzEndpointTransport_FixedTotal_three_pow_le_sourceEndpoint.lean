-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.three_pow_le_sourceEndpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:59:28.029365+00:00
-- url     : https://prove2.me/submissions/3194d457-c9de-412e-acbe-2882381cc5d1

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalSourceCoding
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpoint_eq_three_pow_add_residueEndpoint

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {M s : ℕ} {x : SourceCode M}
    (hs : sourceCodeOddCount x = s) :
    3 ^ s ≤ sourceEndpoint x := by
  rw [sourceEndpoint_eq_three_pow_add_residueEndpoint, hs]
  exact Nat.le_add_right _ _
end CollatzEndpointTransport.FixedTotal
