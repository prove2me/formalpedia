-- Prove2me | solution 1 for BookProof.ChapterA3m.swap23_spinGenDiag_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:46:53.819748+00:00
-- url     : https://prove2.me/submissions/c6655ecd-4d9c-4cfd-9bd7-456793702060

-- Generated from ChapterA3m.lean — solution of BookProof.ChapterA3m.swap23_spinGenDiag_comm
import Mathlib
import Definitions.Def_ChapterA3m
import Theorems.Thm_BookProof_ChapterA3m_swap23_kronecker
open BookProof.ChapterA3m



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k BookProof.ChapterA3l

set_option maxHeartbeats 1000000 in
theorem solution (μ ν : Fin 4) :
    swap23 * spinGenDiag3 μ ν = spinGenDiag3 μ ν * swap23 := by

  unfold spinGenDiag3;
  simp only [mul_add];
  rw [ swap23_kronecker, swap23_kronecker, swap23_kronecker ];
  rw [ add_mul, add_mul ] ; abel_nf;
