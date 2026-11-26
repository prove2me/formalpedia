-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiRate_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:16:08.337396+00:00
-- url     : https://prove2.me/submissions/8786cf72-5d67-4ccb-a2b8-8e0c207fe229

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_OptimizedLinearPullback_psi_pos


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real Topology
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralPullbackSourceCodeDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta D : ℝ} (htheta : 0 < theta) (hD : 0 < D) :
    0 < centralRenyiRate theta D := by
  unfold centralRenyiRate
  exact mul_pos (div_pos htheta (by linarith))
    (OptimizedLinearPullback.psi_pos hD)
end CollatzEndpointTransport.FixedTotal
