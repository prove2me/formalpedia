-- Prove2me | solution 1 for FD1D.V5.log_one_add_two_mul_div_le_parameterA_div_two_thousand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:06:32.263041+00:00
-- url     : https://prove2.me/submissions/b37f7851-37d3-458c-8c5c-d5f4a5e6f754

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_V5_Parameters
import Theorems.Thm_FD1D_V5_parameterA_pos
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero



set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics
namespace FD1D.V5
theorem _root_.solution
    {m : ℕ} (hm : 1 ≤ m) :
    Real.log
        (1 + 2 * (m : ℝ) / (parameterA m : ℝ)) ≤
      (parameterA m : ℝ) / 2000 := by
  have haNat : 2 ≤ parameterA m := by
    have := parameterA_pos hm
    unfold parameterA at *
    omega
  have ha : (2 : ℝ) ≤ parameterA m := by exact_mod_cast haNat
  have hratio :
      2 * (m : ℝ) / (parameterA m : ℝ) ≤ m := by
    calc
      2 * (m : ℝ) / (parameterA m : ℝ)
          ≤ 2 * (m : ℝ) / 2 := by
            gcongr
      _ = m := by ring
  have hlog :
      Real.log (1 + 2 * (m : ℝ) / (parameterA m : ℝ)) ≤
        Real.log (((m + 1 : ℕ) : ℝ)) := by
    apply Real.strictMonoOn_log.monotoneOn
    · exact Set.mem_Ioi.mpr (by positivity)
    · exact Set.mem_Ioi.mpr (by positivity)
    · norm_num at hratio ⊢
      linarith
  have hlog_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_two_le_one : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1
    norm_num
  have hlog_nonneg :
      0 ≤ Real.log (((m + 1 : ℕ) : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ m + 1 by omega))
  have hlog_le_logb :
      Real.log (((m + 1 : ℕ) : ℝ)) ≤
        Real.logb 2 (((m + 1 : ℕ) : ℝ)) := by
    rw [← Real.log_div_log]
    apply (le_div_iff₀ hlog_two_pos).2
    nlinarith
  have hlogb_le_clog :
      Real.logb 2 (((m + 1 : ℕ) : ℝ)) ≤
        (Nat.clog 2 (m + 1) : ℝ) := by
    rw [← Real.natCeil_logb_natCast]
    exact Nat.le_ceil _
  calc
    Real.log
        (1 + 2 * (m : ℝ) / (parameterA m : ℝ))
        ≤ (Nat.clog 2 (m + 1) : ℝ) :=
      hlog.trans (hlog_le_logb.trans hlogb_le_clog)
    _ = (parameterA m : ℝ) / 2000 := by
      simp [parameterA]
end FD1D.V5
