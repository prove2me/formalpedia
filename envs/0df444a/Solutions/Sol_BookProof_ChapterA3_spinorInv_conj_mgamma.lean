-- Prove2me | solution 1 for BookProof.ChapterA3.spinorInv_conj_mgamma
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:36:28.179388+00:00
-- url     : https://prove2.me/submissions/317a3b3d-3b22-42e2-8289-e06849ba4478

-- Generated from ChapterA3i.lean — solution of BookProof.ChapterA3.spinorInv_conj_mgamma
import Mathlib
import Definitions.Def_ChapterA3i
import Definitions.Def_ChapterA3h
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (T : Matrix (Fin 2) (Fin 2) ℂ) (μ : Fin 4) :
    SpinorInv T * mgamma μ * Spinor T = ∑ ν, UpsilonC T ν μ • mgamma ν := by

  unfold SpinorInv Spinor UpsilonC mgamma;
  simp only [SigmaC, SigmaZ, Int.reduceNeg, RingHom.mapMatrix_apply, Int.coe_castRingHom, Treal,
    adj2, Fin.isValue, of_apply, cons_val', cons_val_zero, empty_val', cons_val_fin_one,
    cons_val_one, Complex.neg_re, Complex.ofReal_neg, Complex.neg_im, neg_neg,
    Algebra.mul_smul_comm, mgammaZ, Algebra.smul_mul_assoc, pauliCoeff, trace, diag, pauliσ,
    mul_apply, conjTranspose_apply, RCLike.star_def, Fin.sum_univ_two, Fin.sum_univ_four,
    one_mul, zero_mul, add_zero, zero_add, neg_mul, neg_add_rev];
  rw [ ← Matrix.ext_iff ] at *;
  fin_cases μ <;> simp [ Fin.sum_univ_succ, Matrix.mul_apply ] at *;
  · simp [ Fin.forall_fin_succ, Complex.ext_iff ] at *;
    grind;
  · norm_num [ Fin.forall_fin_succ, Complex.ext_iff ] at *;
    grind;
  · simp [ Fin.forall_fin_succ, Complex.ext_iff ] at *;
    grind;
  · simp [ Fin.forall_fin_succ, Complex.ext_iff ] at *;
    grind
