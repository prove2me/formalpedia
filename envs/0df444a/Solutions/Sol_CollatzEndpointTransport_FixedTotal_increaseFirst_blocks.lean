-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:21:47.956855+00:00
-- url     : https://prove2.me/submissions/c686694c-8e9f-4b0b-836e-2ee75686c349

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCompositionRecurrence

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N : ℕ} (hN : 0 < N) (c : Composition N) :
    (increaseFirst hN c).blocks =
      (c.blocks.head (composition_blocks_ne_nil hN c) + 1) :: c.blocks.tail :=
  rfl
end CollatzEndpointTransport.FixedTotal
