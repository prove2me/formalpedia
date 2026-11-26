-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedRenyiMoment_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:44:21.434173+00:00
-- url     : https://prove2.me/submissions/bc0dd07d-9f23-49b8-b079-540d399a0daf

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedRenyiNumerator_le

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralMomentCompositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (N s : ℕ) {theta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta ≤ 1) :
    fixedRenyiMoment N s theta ≤
      4 * fixedLiftMoment N s theta /
        ((fixedSet N s).card : ℝ) ^ (1 + theta) := by
  unfold fixedRenyiMoment
  exact div_le_div_of_nonneg_right
    (fixedRenyiNumerator_le N s htheta0 htheta1)
    (Real.rpow_nonneg (by positivity) _)
end CollatzEndpointTransport.FixedTotal
