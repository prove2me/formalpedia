-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiShellConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:40:19.258866+00:00
-- url     : https://prove2.me/submissions/66b8a7e2-f2b4-460d-b8ad-727dd10670cc

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralMomentConstant_pos


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real Topology
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralPullbackSourceCodeDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {C D theta eta transport : ℝ}
    (hC : 0 < C)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2) :
    0 < centralRenyiShellConstant C theta eta transport D := by
  unfold centralRenyiShellConstant centralRenyiLargeShellConstant
  have hmoment := centralMomentConstant_pos htheta0 htheta1 heta0 heta1
  have hterm1 : 0 ≤ 4 * ((eta * Real.log 2 / 16)⁻¹) := by positivity
  have hterm2 : 0 ≤ (3 : ℝ) ^ theta *
      centralMomentConstant theta eta *
        (64 * ((((1 - centralRenyiAbsorption theta transport) *
          centralRenyiRate theta D / 6)⁻¹) ^ 6)) := by positivity
  nlinarith [Real.exp_pos
    (centralRenyiShellRate theta transport D *
      centralRenyiStartupIndex theta eta)]
end CollatzEndpointTransport.FixedTotal
