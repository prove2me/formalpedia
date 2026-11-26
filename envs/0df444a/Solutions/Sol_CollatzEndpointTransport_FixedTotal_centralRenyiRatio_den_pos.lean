-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiRatio_den_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:30:37.013343+00:00
-- url     : https://prove2.me/submissions/be939b0f-dee9-4720-a8d0-f2cbb25bfb3a

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
    {theta pi : ℝ} (htheta : 0 < theta) (hpi : 0 < pi) :
    0 < (2 : ℝ) ^ theta - 1 + pi := by
  linarith [one_lt_two_rpow htheta]
end CollatzEndpointTransport.FixedTotal
