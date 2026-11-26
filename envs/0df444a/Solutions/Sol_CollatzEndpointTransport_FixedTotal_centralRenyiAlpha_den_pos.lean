-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiAlpha_den_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:33:01.721824+00:00
-- url     : https://prove2.me/submissions/752d4750-1cee-4700-ab5b-ae8c16f85893

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_one_lt_three_rpow

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta : ℝ} (htheta : 0 < theta) :
    0 < (3 : ℝ) ^ theta - 1 := by
  linarith [one_lt_three_rpow htheta]
end CollatzEndpointTransport.FixedTotal
