-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiGap_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:32:33.81079+00:00
-- url     : https://prove2.me/submissions/97968f89-64bd-4867-b180-95149157f93a

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
    0 < centralRenyiGap theta eta := by
  unfold centralRenyiGap
  linarith
end CollatzEndpointTransport.FixedTotal
