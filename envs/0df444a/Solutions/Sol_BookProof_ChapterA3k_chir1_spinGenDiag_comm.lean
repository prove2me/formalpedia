-- Prove2me | solution 1 for BookProof.ChapterA3k.chir1_spinGenDiag_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:38:40.022549+00:00
-- url     : https://prove2.me/submissions/3e64ae2c-db84-4f7d-9868-717902a372f9

-- Generated from ChapterA3k.lean — solution of BookProof.ChapterA3k.chir1_spinGenDiag_comm
import Mathlib
import Definitions.Def_ChapterA3k
import Theorems.Thm_BookProof_ChapterA3j_chir_spinGen_comm
open BookProof.ChapterA3k



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j

set_option maxHeartbeats 1000000 in
theorem solution (μ ν : Fin 4) :
    chir1 * spinGenDiag μ ν = spinGenDiag μ ν * chir1 := by

      unfold spinGenDiag chir1;
      simp only [mul_add, add_mul, ← mul_kronecker_mul];
      simp [ BookProof.ChapterA3j.chir_spinGen_comm ]
