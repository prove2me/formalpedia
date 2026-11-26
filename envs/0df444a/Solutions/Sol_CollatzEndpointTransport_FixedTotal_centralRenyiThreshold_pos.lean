-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiThreshold_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:17:20.784376+00:00
-- url     : https://prove2.me/submissions/a917068f-47f5-4ea1-927d-721e2f21f6bf

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
    (theta D : ℝ) (M : ℕ) :
    0 < centralRenyiThreshold theta D M :=
  Real.exp_pos _
end CollatzEndpointTransport.FixedTotal
