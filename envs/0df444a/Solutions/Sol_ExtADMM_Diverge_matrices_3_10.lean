-- Prove2me | solution 1 for ExtADMM.Diverge.matrices_3_10
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:05:20.699618+00:00
-- url     : https://prove2.me/submissions/247edff1-1d04-42ba-832f-e8d12b412669

import Mathlib
import Definitions.Def_ExtADMM_Diverge_Setting
set_option autoImplicit false
open Matrix Filter Topology
open ExtADMM.Diverge

theorem solution :
    Lmat a310_2 a310_3 = L310 ∧ Rmat a310_1 a310_2 a310_3 = R310 ∧
      L310.det = 54 ∧ L310⁻¹ * R310 = M310 := by
  have hL : Lmat a310_2 a310_3 = L310 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Lmat, L310, a310_2, a310_3, dotProduct, Fin.sum_univ_succ] <;> norm_num
  have hR : Rmat a310_1 a310_2 a310_3 = R310 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Rmat, R310, a310_1, a310_2, a310_3, dotProduct, Fin.sum_univ_succ,
        Matrix.vecMulVec_apply] <;> norm_num
  have hdet : L310.det = 54 := by
    simp [L310, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    norm_num
  refine ⟨hL, hR, hdet, ?_⟩
  have hunit : IsUnit L310.det := by rw [hdet]; exact IsUnit.mk0 _ (by norm_num)
  have hLM : L310 * M310 = R310 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [L310, M310, R310, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
  calc L310⁻¹ * R310 = L310⁻¹ * (L310 * M310) := by rw [hLM]
    _ = M310 := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mul]
