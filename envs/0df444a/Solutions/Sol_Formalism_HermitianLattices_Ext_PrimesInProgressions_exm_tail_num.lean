-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_tail_num
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:42.550852+00:00
-- url     : https://prove2.me/submissions/b5468459-c16d-4a31-a748-0b9bcd5b500a

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplMainA
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exm_log_y

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (C₃ T T' y l : ℝ) (hC₃ : 0 ≤ C₃) (hT : 2 ≤ T) (hT' : T ≤ T') (hy : 2 ≤ y) (hl : 1 ≤ l) :
    1 / (2 * Real.pi * y) * (2 * (Real.log y + C₃) * (Real.exp 1 * y) / T') ≤
      (1 + 2 * C₃) * (Real.log y * l ^ 2 / T) := by
  have hy0 : 0 < y := by linarith
  have hT0 : 0 < T := by linarith
  have hT'0 : 0 < T' := by linarith
  have hyne : y ≠ 0 := hy0.ne'
  have hT'ne : T' ≠ 0 := hT'0.ne'
  have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
  have hLy : 1 / 2 ≤ Real.log y := exm_log_y y hy
  have hepi : Real.exp 1 ≤ Real.pi := by linarith [Real.exp_one_lt_d9, Real.pi_gt_three]
  have key : 1 / (2 * Real.pi * y) * (2 * (Real.log y + C₃) * (Real.exp 1 * y) / T') =
      (Real.log y + C₃) * (Real.exp 1 / (Real.pi * T')) := by
    field_simp
  have hprod : Real.exp 1 * T ≤ 1 * (Real.pi * T') := by
    rw [one_mul]; exact mul_le_mul hepi hT' hT0.le Real.pi_pos.le
  have h1 : Real.exp 1 / (Real.pi * T') ≤ 1 / T := by
    rw [div_le_div_iff₀ (mul_pos Real.pi_pos hT'0) hT0]; exact hprod
  have hl2 : 1 ≤ l ^ 2 := by nlinarith
  have hA : 0 ≤ (1 + 2 * C₃) * Real.log y := mul_nonneg (by linarith) (by linarith)
  have hnum : Real.log y + C₃ ≤ (1 + 2 * C₃) * Real.log y * l ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hl2 hA, mul_le_mul_of_nonneg_left hLy hC₃]
  rw [key]
  calc (Real.log y + C₃) * (Real.exp 1 / (Real.pi * T')) ≤ (Real.log y + C₃) * (1 / T) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
    _ ≤ (1 + 2 * C₃) * Real.log y * l ^ 2 * (1 / T) :=
        mul_le_mul_of_nonneg_right hnum (one_div_pos.2 hT0).le
    _ = (1 + 2 * C₃) * (Real.log y * l ^ 2 / T) := by ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions
