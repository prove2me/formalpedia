-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiRatio_lt_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:59:00.238019+00:00
-- url     : https://prove2.me/submissions/3c48f7f7-9ec4-4240-a9e3-0706e0059706

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAlpha_den_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRatio_den_pos

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta pi : ℝ}
    (htheta : 0 < theta) (hpi : 0 < pi) :
    centralRenyiRatio theta pi < 1 ↔
      pi < centralRenyiAlpha theta := by
  have hden := centralRenyiRatio_den_pos htheta hpi
  have hthree : 0 < (3 : ℝ) ^ theta - 1 :=
    centralRenyiAlpha_den_pos htheta
  unfold centralRenyiRatio centralRenyiAlpha
  rw [div_lt_one hden, lt_div_iff₀ hthree]
  constructor <;> intro h <;> nlinarith
end CollatzEndpointTransport.FixedTotal
