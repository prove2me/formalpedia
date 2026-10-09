-- Prove2me | solution 1 for BookProof.ChapterA3n.projSym_parityDiag_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:50:36.359955+00:00
-- url     : https://prove2.me/submissions/98151239-a3f8-4e23-a00e-3115e886397d

-- Generated from ChapterA3n.lean — solution of BookProof.ChapterA3n.projSym_parityDiag_comm
import Mathlib
import Definitions.Def_ChapterA3n
import Theorems.Thm_BookProof_ChapterA3n_projSym_uniform_comm
open BookProof.ChapterA3n



open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j

set_option maxHeartbeats 1000000 in
theorem solution {N : ℕ} :
    projSym N * uniform (mgamma 0) = uniform (mgamma 0) * projSym N := projSym_uniform_comm _
