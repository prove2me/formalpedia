-- Prove2me | solution 1 for Corless.det_CM_succ_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:42:53.322836+00:00
-- url     : https://prove2.me/submissions/2efc946e-e38c-4a41-8742-d8c69a7896c6

module
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
public import Definitions.Def_LeanPool_CorlessNilpotent_Matrix
public import Theorems.Thm_Corless_CM_apply
public import Theorems.Thm_Corless_Dv_one
public import Theorems.Thm_Corless_Dv_zero
attribute [local simp] Corless.Dv_one
attribute [local simp] Corless.Dv_zero



set_option autoImplicit true
@[expose] public section
public section
open Polynomial Matrix
open Corless
namespace Corless
theorem _root_.solution (m : ℕ) (u : ℕ → ℂ) :
    (CM (m + 2) u).det = X * (CM (m + 1) (fun i => u (i + 1))).det
      + C (u 0 ^ 2) * (CM m (fun i => u (i + 2))).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ,
    Finset.sum_eq_single (0 : Fin (m + 1))]
  rotate_left
  · intro i _ hi
    refine Fin.cases (fun h => (h rfl).elim) (fun j _ => ?_) i hi
    have hz : CM (m + 2) u j.succ.succ 0 = 0 := by
      simp [CM_apply, Fin.ext_iff, Fin.val_succ]
    rw [hz, mul_zero, zero_mul]
  · simp
  -- first minor: rows and columns 1, …, m+1
  have hA : (CM (m + 2) u).submatrix (Fin.succAbove (0 : Fin (m + 2))) Fin.succ
      = CM (m + 1) (fun i => u (i + 1)) := by
    ext i j
    simp [CM_apply, Fin.ext_iff, Fin.val_succ]
  -- second minor: rows 0, 2, …, m+1 and columns 1, …, m+1; its first row is (-u 0, 0, …, 0)
  have hB : ((CM (m + 2) u).submatrix (Fin.succAbove (Fin.succ (0 : Fin (m + 1)))) Fin.succ).det
      = -C (u 0) * (CM m (fun i => u (i + 2))).det := by
    rw [Fin.succ_zero_eq_one, Matrix.det_succ_row_zero,
      Finset.sum_eq_single (0 : Fin (m + 1))]
    rotate_left
    · intro j _ hj
      refine Fin.cases (fun h => (h rfl).elim) (fun i _ => ?_) j hj
      have hz :
          (CM (m + 2) u).submatrix (Fin.succAbove (1 : Fin (m + 2))) Fin.succ 0 i.succ = 0 := by
        simp only [submatrix_apply, CM_apply]
        have e0 : (Fin.succAbove (1 : Fin (m + 2))) 0 = 0 := rfl
        rw [e0]
        simp [Fin.ext_iff, Fin.val_succ]
      rw [hz, mul_zero, zero_mul]
    · simp
    have hC : ((CM (m + 2) u).submatrix (Fin.succAbove (1 : Fin (m + 2))) Fin.succ).submatrix
        Fin.succ (Fin.succAbove (0 : Fin (m + 1))) = CM m (fun i => u (i + 2)) := by
      ext i j
      simp only [Fin.zero_succAbove, submatrix_apply, CM_apply]
      have e1 : (Fin.succAbove (1 : Fin (m + 2))) i.succ = i.succ.succ := by
        rw [Fin.succAbove_of_le_castSucc]
        simp [Fin.le_iff_val_le_val]
      rw [e1]
      simp [Fin.ext_iff, Fin.val_succ]
    have h00 :
        (CM (m + 2) u).submatrix (Fin.succAbove (1 : Fin (m + 2))) Fin.succ 0 0 = -C (u 0) := by
      simp only [submatrix_apply, CM_apply]
      have e0 : (Fin.succAbove (1 : Fin (m + 2))) 0 = 0 := rfl
      rw [e0]
      simp
    rw [hC, h00]
    simp
  have h00 : CM (m + 2) u 0 0 = X := by simp [CM_apply]
  have h10 : CM (m + 2) u (Fin.succ 0) 0 = C (u 0) := by simp [CM_apply]
  rw [hA, hB, h00, h10]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, zero_add, pow_one, C_pow]
  ring
end Corless
