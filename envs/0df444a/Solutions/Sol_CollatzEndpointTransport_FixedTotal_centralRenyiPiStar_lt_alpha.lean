-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiPiStar_lt_alpha
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:33:42.352939+00:00
-- url     : https://prove2.me/submissions/8d16de06-4eb9-4d2f-8305-fed702a1029f

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiGap_pos

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta eta : ℝ}
    (heta : eta < centralRenyiAlpha theta - 1 / 2) :
    centralRenyiPiStar theta eta < centralRenyiAlpha theta := by
  unfold centralRenyiPiStar
  linarith [centralRenyiGap_pos heta]
end CollatzEndpointTransport.FixedTotal
