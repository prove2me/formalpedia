-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiStageConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:20.030871+00:00
-- url     : https://prove2.me/submissions/ece8b8d5-d933-443b-806b-dbead57e3f3e

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAbsorption_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAbsorption_lt_one
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiDenominatorFloor_pos
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
    {theta eta transport : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta) :
    0 < centralRenyiStageConstant theta eta transport := by
  have hden := centralRenyiDenominatorFloor_pos htheta0 heta0 heta1
  have hmoment := centralMomentConstant_pos htheta0 htheta1 heta0 heta1
  have hfactor : 0 ≤ centralRenyiInverseRateFactor theta transport := by
    unfold centralRenyiInverseRateFactor
    have hz0 := centralRenyiAbsorption_pos htheta0 htransport0
    have hz1 := centralRenyiAbsorption_lt_one htheta0 htransport
    exact pow_nonneg (mul_nonneg
      (div_nonneg (by norm_num) (sub_nonneg.mpr hz1.le))
      (by positivity)) _
  unfold centralRenyiStageConstant centralRenyiStageShellConstant
  positivity
end CollatzEndpointTransport.FixedTotal
