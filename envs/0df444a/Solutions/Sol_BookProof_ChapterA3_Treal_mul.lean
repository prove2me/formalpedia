-- Prove2me | solution 1 for BookProof.ChapterA3.Treal_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:34:19.731291+00:00
-- url     : https://prove2.me/submissions/9a994ce1-664e-4702-ad8d-6aac127714c7

-- Generated from ChapterA3i.lean — solution of BookProof.ChapterA3.Treal_mul
import Mathlib
import Definitions.Def_ChapterA3i
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    Treal (A * B) = Treal A * Treal B := by

  unfold Treal;
  ext i j;    fin_cases i <;> fin_cases j <;> simp [ Matrix.mul_apply, Fin.sum_univ_succ ] <;> ring;
