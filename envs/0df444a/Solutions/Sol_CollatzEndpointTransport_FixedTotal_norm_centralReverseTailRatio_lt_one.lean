-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.norm_centralReverseTailRatio_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:46:04.396069+00:00
-- url     : https://prove2.me/submissions/ab0d169b-8cc7-45d2-9611-cd3a4d10815a

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralReverseTailRatio_nonneg
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralReverseTailRatio_lt_one

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta pi : ℝ} (htheta : 0 < theta)
    (hpi0 : 0 ≤ pi) (hpi1 : pi ≤ 1) :
    ‖centralReverseTailRatio theta pi‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg
    (centralReverseTailRatio_nonneg hpi1)]
  exact centralReverseTailRatio_lt_one htheta hpi0
end CollatzEndpointTransport.FixedTotal
