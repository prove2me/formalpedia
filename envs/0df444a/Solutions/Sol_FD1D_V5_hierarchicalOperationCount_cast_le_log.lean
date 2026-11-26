-- Prove2me | solution 1 for FD1D.V5.hierarchicalOperationCount_cast_le_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:49:01.26316+00:00
-- url     : https://prove2.me/submissions/f7c6e014-37dd-4036-843b-aa9ba5709d37

import Definitions.Def_FD1D_V5_Parameters
import Definitions.Def_FD1D_V5_Complexity
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_V5_parameterA_cast_ge_treeDepth
import Theorems.Thm_FD1D_V5_parameterA_cast_le_logb
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero



set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics
namespace FD1D.V5
theorem _root_.solution
    {m : ℕ} (hm : 2 ≤ m) :
    (hierarchicalOperationCount m : ℝ) ≤
      (100 / Real.log 2) * Real.log (m : ℝ) := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogMono : Real.log 2 ≤ Real.log (m : ℝ) := by
    apply Real.log_le_log
    · norm_num
    · exact_mod_cast hm
  have hdepth :
      (20 : ℝ) * treeDepth m ≤
        (80 / Real.log 2) * Real.log (m : ℝ) := by
    have hscaled :
        (20 : ℝ) * treeDepth m ≤ (parameterA m : ℝ) / 100 := by
      have hparameter :=
        parameterA_cast_ge_treeDepth (show 1 ≤ m by omega)
      nlinarith
    have hparameterLogb := parameterA_cast_le_logb hm
    have hparameterLog :
        (parameterA m : ℝ) ≤
          (8000 / Real.log 2) * Real.log (m : ℝ) := by
      calc
        (parameterA m : ℝ) ≤
            8000 * (Real.log (m : ℝ) / Real.log 2) := by
          simpa [Real.logb] using hparameterLogb
        _ = (8000 / Real.log 2) * Real.log (m : ℝ) := by ring
    calc
      (20 : ℝ) * treeDepth m ≤ (parameterA m : ℝ) / 100 := hscaled
      _ ≤ ((8000 / Real.log 2) * Real.log (m : ℝ)) / 100 :=
        div_le_div_of_nonneg_right hparameterLog (by norm_num)
      _ = (80 / Real.log 2) * Real.log (m : ℝ) := by ring
  have hroot :
      (20 : ℝ) ≤ (20 / Real.log 2) * Real.log (m : ℝ) := by
    calc
      (20 : ℝ) = (20 / Real.log 2) * Real.log 2 := by
        field_simp
      _ ≤ (20 / Real.log 2) * Real.log (m : ℝ) := by
        exact mul_le_mul_of_nonneg_left hlogMono
          (div_nonneg (by norm_num) hlogTwo.le)
  rw [hierarchicalOperationCount, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_add, Nat.cast_one]
  calc
    (20 : ℝ) * ((treeDepth m : ℝ) + 1) =
        (20 : ℝ) * treeDepth m + 20 := by ring
    _ ≤ (80 / Real.log 2) * Real.log (m : ℝ) +
        (20 / Real.log 2) * Real.log (m : ℝ) :=
      add_le_add hdepth hroot
    _ = (100 / Real.log 2) * Real.log (m : ℝ) := by ring
end FD1D.V5
