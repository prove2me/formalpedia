-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.prependOne_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:21:48.934024+00:00
-- url     : https://prove2.me/submissions/22aa127e-963a-4146-82da-d5b0aebbb35e

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCompositionRecurrence

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N : ℕ} (c : Composition N) :
    (prependOne c).blocks = 1 :: c.blocks :=
  rfl
end CollatzEndpointTransport.FixedTotal
