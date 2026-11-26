-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiRatio_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:40:31.99144+00:00
-- url     : https://prove2.me/submissions/c0339353-ca37-44bb-9f14-7c17b306446d

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_one_lt_two_rpow
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRatio_den_pos_of_nonneg

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta pi rho : ℝ}
    (htheta : 0 < theta) (hpi : 0 ≤ pi) (hpirho : pi ≤ rho) :
    centralRenyiRatio theta pi ≤ centralRenyiRatio theta rho := by
  have hrho : 0 ≤ rho := hpi.trans hpirho
  have htwo : 0 < (2 : ℝ) ^ theta - 1 := by
    linarith [one_lt_two_rpow htheta]
  have hthree : 0 < (3 : ℝ) ^ theta := by positivity
  have hdenPi := centralRenyiRatio_den_pos_of_nonneg htheta hpi
  have hdenRho := centralRenyiRatio_den_pos_of_nonneg htheta hrho
  unfold centralRenyiRatio
  rw [div_le_div_iff₀ hdenPi hdenRho]
  nlinarith [mul_nonneg hthree.le htwo.le]
end CollatzEndpointTransport.FixedTotal
