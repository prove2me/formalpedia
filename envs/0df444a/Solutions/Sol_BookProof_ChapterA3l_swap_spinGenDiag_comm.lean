-- Prove2me | solution 1 for BookProof.ChapterA3l.swap_spinGenDiag_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:02:08.154138+00:00
-- url     : https://prove2.me/submissions/71c63290-4af0-484b-92ee-35024677a38e

-- Generated from ChapterA3l.lean — solution of BookProof.ChapterA3l.swap_spinGenDiag_comm
import Mathlib
import Definitions.Def_ChapterA3l
import Theorems.Thm_BookProof_ChapterA3l_swap_kronecker
open BookProof.ChapterA3l



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k

set_option maxHeartbeats 1000000 in
theorem solution (μ ν : Fin 4) :
    BookProof.ChapterA3l.swap * spinGenDiag μ ν = spinGenDiag μ ν * BookProof.ChapterA3l.swap := by

  unfold spinGenDiag
  rw [mul_add, add_mul, swap_kronecker, swap_kronecker, add_comm]
