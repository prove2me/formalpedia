-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiPiStar_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:39:24.352656+00:00
-- url     : https://prove2.me/submissions/fcbf8cf0-8ee9-45e3-adff-15a3adfd1aed

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_one_half_add_eta_lt_centralRenyiPiStar

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
    0 < centralRenyiPiStar theta eta := by
  linarith [one_half_add_eta_lt_centralRenyiPiStar heta1]
end CollatzEndpointTransport.FixedTotal
