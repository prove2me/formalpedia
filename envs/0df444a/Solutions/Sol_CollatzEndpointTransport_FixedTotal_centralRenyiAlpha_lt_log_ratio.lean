-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiAlpha_lt_log_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:38:31.183839+00:00
-- url     : https://prove2.me/submissions/a9c2a38a-e6e5-4f5b-bfcd-5c7e5b880614

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAlpha_den_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_exp_sub_one_div_lt
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta : ℝ} (htheta0 : 0 < theta) :
    centralRenyiAlpha theta < Real.log 2 / Real.log 3 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hxy : theta * Real.log 2 < theta * Real.log 3 :=
    mul_lt_mul_of_pos_left (Real.strictMonoOn_log (by norm_num) (by norm_num)
      (by norm_num)) htheta0
  have hslope := exp_sub_one_div_lt (mul_pos htheta0 hlog2) hxy
  have hexp2 : Real.exp (theta * Real.log 2) = (2 : ℝ) ^ theta := by
    simp [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
  have hexp3 : Real.exp (theta * Real.log 3) = (3 : ℝ) ^ theta := by
    simp [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), mul_comm]
  rw [hexp2, hexp3] at hslope
  unfold centralRenyiAlpha
  rw [div_lt_div_iff₀ (centralRenyiAlpha_den_pos htheta0) hlog3]
  rw [div_lt_div_iff₀ (mul_pos htheta0 hlog2) (mul_pos htheta0 hlog3)] at hslope
  nlinarith
end CollatzEndpointTransport.FixedTotal
