-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiAsymptoticRate_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:09:06.4101+00:00
-- url     : https://prove2.me/submissions/7043457c-d387-401f-89c5-e4dbea025d78

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real Topology
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralPullbackSourceCodeDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta : ℝ} (htheta : 0 < theta) :
    0 < centralRenyiAsymptoticRate theta := by
  unfold centralRenyiAsymptoticRate
  exact mul_pos (div_pos htheta (by linarith))
    (div_pos (Real.log_pos (by norm_num))
      (mul_pos (by norm_num) (Real.log_pos (by norm_num))))
end CollatzEndpointTransport.FixedTotal
