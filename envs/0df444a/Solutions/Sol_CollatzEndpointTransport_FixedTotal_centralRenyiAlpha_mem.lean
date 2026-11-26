-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiAlpha_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:58:57.298799+00:00
-- url     : https://prove2.me/submissions/54f2c6f8-2ffe-47f5-b1a9-df6bce7a97d7

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_one_half_lt_centralRenyiAlpha
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAlpha_lt_log_ratio

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta : ℝ} (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    centralRenyiAlpha theta ∈
      Set.Ioo (1 / 2 : ℝ) (Real.log 2 / Real.log 3) :=
  ⟨one_half_lt_centralRenyiAlpha htheta0 htheta1,
    centralRenyiAlpha_lt_log_ratio htheta0⟩
end CollatzEndpointTransport.FixedTotal
