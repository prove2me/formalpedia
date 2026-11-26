-- Prove2me | solution 1 for FD1D.two_hundred_mul_log_one_add_div_parameterA_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:01:37.059689+00:00
-- url     : https://prove2.me/submissions/790e9ba8-777c-43ca-a95d-c4d5deea857f

import Definitions.Def_FD1D_Potential
import Definitions.Def_FD1D_Parameters
import Definitions.Def_FD1D_PotentialBounds
import Theorems.Thm_FD1D_two_hundred_mul_log_one_add_le_parameterA
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_harmonicPotential_zero
import Theorems.Thm_FD1D_leafCount_eq_pow
import Theorems.Thm_FD1D_natFloor_parameterRatio
import Theorems.Thm_FD1D_parameterA_cast_pos
import Theorems.Thm_FD1D_policyA_eq_parameterA
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.harmonicPotential_zero
attribute [local simp] FD1D.leafCount_eq_pow
attribute [local simp] FD1D.natFloor_parameterRatio
attribute [local simp] FD1D.policyA_eq_parameterA
attribute [local simp] FD1D.weightedLevel_zero



set_option autoImplicit true
open FD1D
noncomputable section
open Set intervalIntegral
open scoped BigOperators
namespace FD1D
theorem _root_.solution
    {m : ℕ} (hm : 1 ≤ m) :
    200 * Real.log
        (1 + (m : ℝ) / (parameterA m : ℝ)) /
        (parameterA m : ℝ) ≤ 1 := by
  apply (div_le_iff₀ (parameterA_cast_pos hm)).2
  simpa using two_hundred_mul_log_one_add_le_parameterA hm
end FD1D
