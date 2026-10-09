-- Prove2me | solution 1 for BookProof.ChapterA3.upsilonC_antihom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:10:46.829808+00:00
-- url     : https://prove2.me/submissions/6e9634f7-b8fc-4f6a-bc54-cc0520a90528

-- Generated from ChapterA3h.lean — solution of BookProof.ChapterA3.upsilonC_antihom
import Mathlib
import Definitions.Def_ChapterA3h
import Theorems.Thm_BookProof_ChapterA3_pauli_expand
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (T U : Matrix (Fin 2) (Fin 2) ℂ) :
    UpsilonC (T * U) = UpsilonC U * UpsilonC T := by

  ext μ ν; simp only [UpsilonC, conjTranspose_mul, of_apply, mul_apply] ;
  have h_expand : Tᴴ * pauliσ ν * T = ∑ x, pauliCoeff (Tᴴ * pauliσ ν * T) x • pauliσ x := by
    convert pauli_expand ( Tᴴ * pauliσ ν * T ) using 1;
  conv_lhs => rw [ show Uᴴ * Tᴴ * pauliσ ν * ( T * U ) = Uᴴ * ( Tᴴ * pauliσ ν * T ) * U
      by simp only [mul_assoc] ];
  conv_lhs => rw [ h_expand ];
  simp [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul, pauliCoeff ]
