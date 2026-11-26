-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.refinedCentralRenyiShellConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:30:01.329116+00:00
-- url     : https://prove2.me/submissions/e7d323ea-ec76-4e9a-ba3c-04d794ac550b

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiMomentTransport
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedArbitraryTargetEndpointTransport
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_refinedCentralRenyiLargeShellConstant_pos

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta eta transport : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta) :
    0 < refinedCentralRenyiShellConstant theta eta transport := by
  unfold refinedCentralRenyiShellConstant
  exact add_pos
    (refinedCentralRenyiLargeShellConstant_pos
      htheta0 htheta1 heta0 heta1 htransport0 htransport)
    (Real.exp_pos _)
end CollatzEndpointTransport.FixedTotal
