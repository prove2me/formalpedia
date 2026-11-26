-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralReverseTailRatio_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:45:14.613732+00:00
-- url     : https://prove2.me/submissions/41ebd480-2abb-4cb9-b0ee-22282ae9b3f1

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_one_lt_two_rpow


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta pi : ℝ} (htheta : 0 < theta)
    (hpi0 : 0 ≤ pi) :
    centralReverseTailRatio theta pi < 1 := by
  unfold centralReverseTailRatio
  have htwo : 1 < (2 : ℝ) ^ theta := one_lt_two_rpow htheta
  rw [div_lt_one (by positivity : 0 < (2 : ℝ) ^ theta)]
  linarith
end CollatzEndpointTransport.FixedTotal
