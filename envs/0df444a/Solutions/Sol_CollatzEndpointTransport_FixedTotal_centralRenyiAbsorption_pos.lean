-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiAbsorption_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:12:05.06418+00:00
-- url     : https://prove2.me/submissions/82bce5dd-50e2-49c6-87ee-dea3661e39d7

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAsymptoticRate_pos

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real Topology
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralPullbackSourceCodeDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta transport : ℝ}
    (htheta : 0 < theta) (htransport : 0 < transport) :
    0 < centralRenyiAbsorption theta transport := by
  unfold centralRenyiAbsorption
  exact div_pos
    (add_pos htransport (centralRenyiAsymptoticRate_pos htheta))
    (mul_pos (by norm_num) (centralRenyiAsymptoticRate_pos htheta))
end CollatzEndpointTransport.FixedTotal
