-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.holderScaleExponent_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:12:09.344577+00:00
-- url     : https://prove2.me/submissions/fb6806a6-90b8-486f-9e02-ba6b1058b628

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
    0 < holderScaleExponent theta := by
  unfold holderScaleExponent
  positivity
end CollatzEndpointTransport.FixedTotal
