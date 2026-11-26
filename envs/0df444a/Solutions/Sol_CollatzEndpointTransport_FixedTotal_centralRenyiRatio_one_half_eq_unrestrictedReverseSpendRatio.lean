-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiRatio_one_half_eq_unrestrictedReverseSpendRatio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:59:11.526372+00:00
-- url     : https://prove2.me/submissions/62ad125d-23e3-462d-835c-5aabc13c081a

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRatio_den_pos

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta : ℝ} (htheta : 0 < theta) :
    centralRenyiRatio theta (1 / 2) =
      unrestrictedReverseSpendRatio theta := by
  have hden1 : 0 < (2 : ℝ) ^ theta - 1 + 1 / 2 :=
    centralRenyiRatio_den_pos htheta (by norm_num)
  have hpow : (2 : ℝ) ^ (1 + theta) = 2 * (2 : ℝ) ^ theta := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  have hdenEq :
      (2 : ℝ) ^ (1 + theta) - 1 =
        2 * ((2 : ℝ) ^ theta - 1 + 1 / 2) := by
    rw [hpow]
    ring
  unfold centralRenyiRatio unrestrictedReverseSpendRatio
  rw [hdenEq]
  field_simp [hden1.ne']
end CollatzEndpointTransport.FixedTotal
