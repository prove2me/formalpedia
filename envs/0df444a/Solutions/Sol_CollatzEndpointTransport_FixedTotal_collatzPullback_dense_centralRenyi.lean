-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.collatzPullback_dense_centralRenyi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:03:25.751922+00:00
-- url     : https://prove2.me/submissions/9306bd4a-c6a3-46b3-bf7c-924ecb8a1422

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAbsorption_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRate_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiShellRate_lt_log_two
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiShellConstant_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_shellBad_collatzPullback_le_centralRenyi
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_IsCDDense_C_pos
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_IsCDDense_D_pos
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_isCDDense_of_shell_bound


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real Topology
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralPullbackSourceCodeDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {S : Set ℕ} {C D theta eta transport : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta)
    (hcutLate : centralRenyiShellRate theta transport D ≤
      eta * Real.log 2 / 16)
    (hcutParity : centralRenyiShellRate theta transport D ≤ eta ^ 2 / 8) :
    QuantitativeDensity.IsCDDense
      (QuantitativeDensity.collatzPullback S)
      (centralRenyiPullbackConstant C theta eta transport D)
      (centralRenyiShellRate theta transport D / Real.log 2) := by
  unfold centralRenyiPullbackConstant
  exact QuantitativeDensity.isCDDense_of_shell_bound
    (centralRenyiShellConstant_pos hS.C_pos htheta0 htheta1 heta0 heta1)
    (mul_pos (centralRenyiAbsorption_pos htheta0 htransport0)
      (centralRenyiRate_pos htheta0 hS.D_pos))
    (centralRenyiShellRate_lt_log_two
      htheta0 htheta1 htransport0 htransport hS.D_pos)
    (shellBad_collatzPullback_le_centralRenyi
      hS htheta0 htheta1 heta0 heta1 htransport0 htransport
      hcutLate hcutParity)
end CollatzEndpointTransport.FixedTotal
