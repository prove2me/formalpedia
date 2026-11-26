-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiAlpha_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:58:48.796792+00:00
-- url     : https://prove2.me/submissions/9fa271b9-656c-42d6-bb9f-94c09e9b5b09

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_one_lt_two_rpow
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAlpha_den_pos

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta : ℝ} (htheta : 0 < theta) :
    0 < centralRenyiAlpha theta := by
  unfold centralRenyiAlpha
  exact div_pos (by linarith [one_lt_two_rpow htheta])
    (centralRenyiAlpha_den_pos htheta)
end CollatzEndpointTransport.FixedTotal
