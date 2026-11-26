-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.shellBad_collatzPullback_le_centralRenyi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:21.927811+00:00
-- url     : https://prove2.me/submissions/8489a4e5-d3ec-4d51-881f-0ae4be47319a

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpointBad_div_pow_le_centralRenyi_absorbed
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_shellBad_collatzPullback_eq_sourceEndpointBad


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
    (hcutParity : centralRenyiShellRate theta transport D ≤ eta ^ 2 / 8)
    (M : ℕ) :
    ((QuantitativeDensity.shellBad
        (QuantitativeDensity.collatzPullback S) M).card : ℝ) ≤
      centralRenyiShellConstant C theta eta transport D *
        Real.exp (-centralRenyiShellRate theta transport D * M) *
        (2 ^ M : ℝ) := by
  rw [card_shellBad_collatzPullback_eq_sourceEndpointBad]
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ M)).mp
    (sourceEndpointBad_div_pow_le_centralRenyi_absorbed
      hS htheta0 htheta1 heta0 heta1 htransport0 htransport
      hcutLate hcutParity M)
end CollatzEndpointTransport.FixedTotal
