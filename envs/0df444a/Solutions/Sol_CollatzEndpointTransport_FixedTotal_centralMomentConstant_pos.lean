-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralMomentConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:45:54.464796+00:00
-- url     : https://prove2.me/submissions/0457eada-1220-4602-a112-a1c5f0623092

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRatio_piStar_lt_one


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2) :
    0 < centralMomentConstant theta eta := by
  have hratio := centralRenyiRatio_piStar_lt_one
    htheta0 htheta1 heta0 heta1
  have hden : 0 < 1 -
      centralRenyiRatio theta (centralRenyiPiStar theta eta) := by
    linarith
  unfold centralMomentConstant
  exact mul_pos (by norm_num)
    (add_pos_of_pos_of_nonneg (div_pos (by positivity) hden) (by norm_num))
end CollatzEndpointTransport.FixedTotal
