-- Prove2me | solution 1 for BookProof.ChapterA3m.swap13_spinGenDiag_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:46:55.073052+00:00
-- url     : https://prove2.me/submissions/68776069-6486-4632-982d-39473ca184e7

-- Generated from ChapterA3m.lean — solution of BookProof.ChapterA3m.swap13_spinGenDiag_comm
import Mathlib
import Definitions.Def_ChapterA3m
import Theorems.Thm_BookProof_ChapterA3m_swap13_kronecker
open BookProof.ChapterA3m



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k BookProof.ChapterA3l

set_option maxHeartbeats 1000000 in
theorem solution (μ ν : Fin 4) :
    swap13 * spinGenDiag3 μ ν = spinGenDiag3 μ ν * swap13 := by

  unfold spinGenDiag3;
  simp only [zero_mul, implies_true, mul_zero, mul_one, kroneckerMap_one_one, Matrix.mul_add,
      Matrix.add_mul];
  have := swap13_kronecker ( spinGen μ ν ) 1 1;    ( have := swap13_kronecker 1 ( spinGen μ ν ) 1; (
      have := swap13_kronecker 1 1 ( spinGen μ ν ) ; simp_all only [zero_mul, implies_true,
          mul_zero, mul_one, kroneckerMap_one_one]  ; ) );
  abel1
