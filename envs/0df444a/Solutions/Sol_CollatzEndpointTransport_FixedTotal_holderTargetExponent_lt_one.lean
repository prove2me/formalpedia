-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.holderTargetExponent_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:02:13.800938+00:00
-- url     : https://prove2.me/submissions/f6237df5-3d29-497d-b1ab-39651f035321

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
    holderTargetExponent theta < 1 := by
  unfold holderTargetExponent
  rw [div_lt_one (by linarith)]
  linarith
end CollatzEndpointTransport.FixedTotal
