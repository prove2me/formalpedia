-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiRatio_den_pos_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:33:37.468214+00:00
-- url     : https://prove2.me/submissions/1b9caa65-7d65-47e7-a9bd-851673faacd7

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_one_lt_two_rpow

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta pi : ℝ} (htheta : 0 < theta) (hpi : 0 ≤ pi) :
    0 < (2 : ℝ) ^ theta - 1 + pi := by
  linarith [one_lt_two_rpow htheta]
end CollatzEndpointTransport.FixedTotal
