-- Prove2me | solution 1 for BookProof.ChapterA3.mgamma_commutant_scalar
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:12:40.502672+00:00
-- url     : https://prove2.me/submissions/3cc6c505-187d-4974-bc08-5d91da2f925c

-- Generated from ChapterPauliCommutant.lean — solution of BookProof.ChapterA3.mgamma_commutant_scalar
import Mathlib
import Definitions.Def_ChapterPauliCommutant
import Definitions.Def_ChapterA3
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution (M : Matrix (Fin 4) (Fin 4) ℂ)
    (h : ∀ μ, M * mgamma μ = mgamma μ * M) :
    M = M 0 0 • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by

  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  rw [← Matrix.ext_iff] at h0 h1 h2 h3
  simp only [mgamma, mgammaZ, Int.reduceNeg, RingHom.mapMatrix_apply, Int.coe_castRingHom,
    mul_apply, map_apply, of_apply, cons_val', cons_val_fin_one, Fin.sum_univ_four,
    Fin.isValue, cons_val_zero, cons_val_one, cons_val, Fin.forall_fin_succ, Int.cast_zero,
    mul_zero, add_zero, Int.cast_neg, Int.cast_one, mul_neg, mul_one, zero_add, cons_val_succ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc, IsEmpty.forall_iff, and_true,
    zero_mul, one_mul, neg_mul, neg_inj, true_and] at h0 h1 h2 h3
  obtain ⟨⟨-, p2, p3, -⟩, ⟨p5, -, -, p8⟩, -, -⟩ := h0
  obtain ⟨⟨q1, q2⟩, ⟨q3, q4⟩, ⟨q5, q6⟩, q7, q8⟩ := h1
  obtain ⟨⟨-, r2, -, -⟩, ⟨r5, -, -, -⟩, -, -⟩ := h2
  obtain ⟨⟨-, s2, -, -⟩, -, -, -⟩ := h3
  have e01 : M 0 1 = 0 := by linear_combination (-1 / 2 : ℂ) * q1
  have e02 : M 0 2 = 0 := by linear_combination (-1 / 2 : ℂ) * q2
  have e10 : M 1 0 = 0 := by linear_combination (1 / 2 : ℂ) * q3
  have e13 : M 1 3 = 0 := by linear_combination (1 / 2 : ℂ) * q4
  have e20 : M 2 0 = 0 := by linear_combination (1 / 2 : ℂ) * q5
  have e23 : M 2 3 = 0 := by linear_combination (1 / 2 : ℂ) * q6
  have e31 : M 3 1 = 0 := by linear_combination (-1 / 2 : ℂ) * q7
  have e32 : M 3 2 = 0 := by linear_combination (-1 / 2 : ℂ) * q8
  have e03 : M 0 3 = 0 := by linear_combination (-1 / 2 : ℂ) * p2 + (1 / 2 : ℂ) * r2
  have e21 : M 2 1 = 0 := by linear_combination -r2 + e03
  have e12 : M 1 2 = 0 := by linear_combination (-1 / 2 : ℂ) * p5 + (1 / 2 : ℂ) * r5
  have e30 : M 3 0 = 0 := by linear_combination -r5 + e12
  have e11 : M 1 1 = M 0 0 := by linear_combination -s2
  have e22 : M 2 2 = M 0 0 := by linear_combination -p3
  have e33 : M 3 3 = M 0 0 := by linear_combination -p8 - s2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e01, e02, e03, e10, e11, e12, e13, e20, e21, e22, e23, e30, e31, e32, e33]
