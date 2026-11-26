-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.holderCentralMomentConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:23:01.979975+00:00
-- url     : https://prove2.me/submissions/e9194243-fd2d-4b99-b062-409dfc3e38c8

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiShellTransport
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralEndpointInformation
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiMomentTransport
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSizeCentralMomentConstant_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fractionalBinomialMassConstant_pos


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2) :
    0 < holderCentralMomentConstant theta eta := by
  unfold holderCentralMomentConstant
  exact Real.rpow_pos_of_pos
    (mul_pos
      (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _))
      (mul_pos
        (fixedSizeCentralMomentConstant_pos htheta0 htheta1 heta0 heta1)
        (fractionalBinomialMassConstant_pos htheta0 htheta1))) _
end CollatzEndpointTransport.FixedTotal
