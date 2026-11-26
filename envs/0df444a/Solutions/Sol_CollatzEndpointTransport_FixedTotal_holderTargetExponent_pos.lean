-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.holderTargetExponent_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:23:39.891195+00:00
-- url     : https://prove2.me/submissions/df0c6fcc-e70c-423f-a322-771197af1056

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiMomentTransport
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedArbitraryTargetEndpointTransport

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta : ℝ} (htheta : 0 < theta) :
    0 < holderTargetExponent theta := by
  unfold holderTargetExponent
  positivity
end CollatzEndpointTransport.FixedTotal
