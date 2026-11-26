-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiAbsorption_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:12:07.975431+00:00
-- url     : https://prove2.me/submissions/4c663398-b7d4-49d8-ab5e-2498ecbb5225

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
    (htheta : 0 < theta)
    (htransport : transport < centralRenyiAsymptoticRate theta) :
    centralRenyiAbsorption theta transport < 1 := by
  unfold centralRenyiAbsorption
  have hlimit := centralRenyiAsymptoticRate_pos htheta
  rw [div_lt_one (by positivity)]
  linarith
end CollatzEndpointTransport.FixedTotal
