-- Prove2me | solution 1 for BookProof.ChapterA3m.projSym3_spinGenDiag_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:47:33.826013+00:00
-- url     : https://prove2.me/submissions/dfc4ba14-ab28-4adf-bd2c-debbed3bccca

-- Generated from ChapterA3m.lean — solution of BookProof.ChapterA3m.projSym3_spinGenDiag_comm
import Mathlib
import Definitions.Def_ChapterA3m
import Theorems.Thm_BookProof_ChapterA3m_swap12_spinGenDiag_comm
import Theorems.Thm_BookProof_ChapterA3m_swap23_spinGenDiag_comm
import Theorems.Thm_BookProof_ChapterA3m_swap13_spinGenDiag_comm
open BookProof.ChapterA3m



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k BookProof.ChapterA3l

set_option maxHeartbeats 1000000 in
theorem solution (μ ν : Fin 4) :
    projSym3 * spinGenDiag3 μ ν = spinGenDiag3 μ ν * projSym3 := by

  unfold projSym3;
  simp [ Matrix.mul_add, add_mul, Matrix.mul_assoc, swap12_spinGenDiag_comm,
      swap23_spinGenDiag_comm, swap13_spinGenDiag_comm ];
  simp only [← mul_assoc, swap12_spinGenDiag_comm, swap23_spinGenDiag_comm]
