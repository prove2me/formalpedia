-- Prove2me | solution 1 for BookProof.ChapterA3.spinor_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:34:48.911664+00:00
-- url     : https://prove2.me/submissions/edca8fc7-3ec9-4915-b199-1ac3d4eab5e9

import Mathlib
import Definitions.Def_ChapterA3i
open BookProof.ChapterA3 Matrix
open scoped ComplexConjugate
set_option maxHeartbeats 0

theorem solution (T : Matrix (Fin 2) (Fin 2) ℂ)
    (hdet : T 0 0 * T 1 1 - T 0 1 * T 1 0 = 1) :
    (Spinor T)⁻¹ = SpinorInv T := by
  apply Matrix.inv_eq_right_inv
  have hr := congrArg Complex.re hdet
  have hi := congrArg Complex.im hdet
  simp [Complex.mul_re, Complex.mul_im] at hr hi
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [Spinor, SpinorInv, SigmaC, SigmaZ, Treal, adj2,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply,
      Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons,
      Complex.mul_re, Complex.mul_im] <;> linarith

#print axioms solution
