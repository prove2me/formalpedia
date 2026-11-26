-- Prove2me | solution 1 for FD1D.two_hundred_mul_log_one_add_le_parameterA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:23:09.275796+00:00
-- url     : https://prove2.me/submissions/316da6ed-e3ae-435b-979e-d6b46864db0a

import Definitions.Def_FD1D_Potential
import Definitions.Def_FD1D_Parameters
import Definitions.Def_FD1D_PotentialBounds
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_harmonicPotential_zero
import Theorems.Thm_FD1D_leafCount_eq_pow
import Theorems.Thm_FD1D_natFloor_parameterRatio
import Theorems.Thm_FD1D_parameterA_cast_pos
import Theorems.Thm_FD1D_parameterA_pos
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
        (1 + (m : ℝ) / (parameterA m : ℝ)) ≤ parameterA m := by
  have ha : 0 < (parameterA m : ℝ) := parameterA_cast_pos hm
  have hratio : (m : ℝ) / parameterA m ≤ m := by
    have haone : (1 : ℝ) ≤ parameterA m := by
      exact_mod_cast (parameterA_pos hm)
    calc
      (m : ℝ) / parameterA m ≤ (m : ℝ) / 1 :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg m) zero_lt_one haone
      _ = m := by ring
  have hlog_m :
      Real.log (1 + (m : ℝ) / parameterA m) ≤
        Real.log ((m + 1 : ℕ) : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · exact Set.mem_Ioi.mpr (by positivity)
    · exact Set.mem_Ioi.mpr (by positivity)
    · norm_num at hratio ⊢
      linarith
  have hlog_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_two_le_one : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1
    norm_num
  have hlog_nat_nonneg :
      0 ≤ Real.log ((m + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ m + 1 by omega))
  have hlog_le_logb :
      Real.log ((m + 1 : ℕ) : ℝ) ≤
        Real.logb 2 ((m + 1 : ℕ) : ℝ) := by
    rw [← Real.log_div_log]
    apply (le_div_iff₀ hlog_two_pos).2
    nlinarith
  have hlogb_le_clog :
      Real.logb 2 ((m + 1 : ℕ) : ℝ) ≤
        (Nat.clog 2 (m + 1) : ℝ) := by
    rw [← Real.natCeil_logb_natCast]
    exact Nat.le_ceil _
  calc
    200 * Real.log
          (1 + (m : ℝ) / (parameterA m : ℝ)) ≤
        200 * (Nat.clog 2 (m + 1) : ℝ) := by
      gcongr
      exact hlog_m.trans (hlog_le_logb.trans hlogb_le_clog)
    _ = parameterA m := by
      simp [parameterA]
end FD1D
