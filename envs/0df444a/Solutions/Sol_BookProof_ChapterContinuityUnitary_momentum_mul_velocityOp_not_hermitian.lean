-- Prove2me | solution 1 for BookProof.ChapterContinuityUnitary.momentum_mul_velocityOp_not_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T21:15:52.377251+00:00
-- url     : https://prove2.me/submissions/20e5c21f-c6c0-400f-9db1-e87399ec2cdd

import Mathlib
import Definitions.Def_ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitary
open scoped BigOperators Matrix TensorProduct

theorem solution :
    (momentum 3 * velocityOp (fun k => (k.val : ℝ)))ᴴ
      ≠ momentum 3 * velocityOp (fun k => (k.val : ℝ)) := by
  set v : ZMod 3 → ℝ := fun k => (k.val : ℝ) with hv
  set M : Matrix (ZMod 3) (ZMod 3) ℂ := momentum 3 * velocityOp v with hM
  have hR : M 0 1 = -Complex.I / 2 := by
    rw [hM, Matrix.mul_apply]
    rw [Finset.sum_eq_single (1 : ZMod 3)]
    · rw [velocityOp, Matrix.diagonal_apply_eq]
      simp only [hv, ZMod.val_one, Complex.ofReal_one, mul_one, momentum]
      rw [if_pos (by decide : (1 : ZMod 3) = 0 + 1), if_neg (by decide : (1 : ZMod 3) ≠ 0 - 1)]
      simp
    · intro k _ hk
      rw [velocityOp, Matrix.diagonal_apply_ne _ hk, mul_zero]
    · intro hk
      exact absurd (Finset.mem_univ (1 : ZMod 3)) hk
  have h10 : M 1 0 = 0 := by
    rw [hM, Matrix.mul_apply]
    rw [Finset.sum_eq_single (0 : ZMod 3)]
    · rw [velocityOp, Matrix.diagonal_apply_eq]
      simp [hv, ZMod.val_zero]
    · intro k _ hk
      rw [velocityOp, Matrix.diagonal_apply_ne _ hk, mul_zero]
    · intro hk
      exact absurd (Finset.mem_univ (0 : ZMod 3)) hk
  have hL : Mᴴ 0 1 = 0 := by
    rw [Matrix.conjTranspose_apply, h10, star_zero]
  intro h
  have h01 := congr_fun (congr_fun h (0 : ZMod 3)) (1 : ZMod 3)
  rw [hL, hR] at h01
  exact absurd h01.symm (div_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) two_ne_zero)
