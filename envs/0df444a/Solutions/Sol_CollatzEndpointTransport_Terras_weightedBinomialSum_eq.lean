-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.weightedBinomialSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:23:25.942276+00:00
-- url     : https://prove2.me/submissions/03c9acd7-ccb7-4d85-b089-254b9ac592ec

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution (H : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range (H + 1), (H.choose k : ℝ) * x ^ k) = (1 + x) ^ H := by
  simpa [add_comm, mul_comm] using (add_pow x 1 H).symm
end CollatzEndpointTransport.Terras
