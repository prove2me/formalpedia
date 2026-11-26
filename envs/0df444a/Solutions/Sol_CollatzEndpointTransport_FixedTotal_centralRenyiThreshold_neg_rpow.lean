-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiThreshold_neg_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:17:23.617025+00:00
-- url     : https://prove2.me/submissions/04ccca66-99d3-4353-b2be-b8e1ae6eca9c

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
    {theta D : ℝ} (M : ℕ) (htheta : 0 < theta) :
    (centralRenyiThreshold theta D M) ^ (-theta) =
      Real.exp (-centralRenyiRate theta D * M) := by
  unfold centralRenyiThreshold centralRenyiRate
  rw [← Real.exp_mul]
  congr 1
  have hden : 0 < 1 + theta := by linarith
  field_simp [hden.ne']
end CollatzEndpointTransport.FixedTotal
