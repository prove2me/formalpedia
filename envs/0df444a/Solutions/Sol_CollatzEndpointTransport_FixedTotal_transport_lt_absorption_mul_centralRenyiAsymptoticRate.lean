-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.transport_lt_absorption_mul_centralRenyiAsymptoticRate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:37:21.77009+00:00
-- url     : https://prove2.me/submissions/124e03a1-29ae-4e0a-9a9d-52a864c1474f

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
    transport < centralRenyiAbsorption theta transport *
      centralRenyiAsymptoticRate theta := by
  unfold centralRenyiAbsorption
  have hlimit := centralRenyiAsymptoticRate_pos htheta
  have heq :
      (transport + centralRenyiAsymptoticRate theta) /
            (2 * centralRenyiAsymptoticRate theta) *
          centralRenyiAsymptoticRate theta =
        (transport + centralRenyiAsymptoticRate theta) / 2 := by
    field_simp [hlimit.ne']
  rw [heq]
  linarith
end CollatzEndpointTransport.FixedTotal
