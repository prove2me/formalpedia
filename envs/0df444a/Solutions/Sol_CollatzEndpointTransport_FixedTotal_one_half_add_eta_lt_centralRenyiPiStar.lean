-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.one_half_add_eta_lt_centralRenyiPiStar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:33:02.362146+00:00
-- url     : https://prove2.me/submissions/32250ef0-0a1b-4dee-8e56-9b07d71e4bb2

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta eta : ℝ}
    (heta : eta < centralRenyiAlpha theta - 1 / 2) :
    1 / 2 + eta < centralRenyiPiStar theta eta := by
  unfold centralRenyiPiStar centralRenyiGap
  linarith
end CollatzEndpointTransport.FixedTotal
