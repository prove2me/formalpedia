-- Prove2me | solution 1 for BookProof.ChapterParityQL.QLParity_pow_four
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:13:08.182258+00:00
-- url     : https://prove2.me/submissions/bf65277e-2748-4bc3-baf1-6881ebf9b479
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterParityQL.lean — solution of BookProof.ChapterParityQL.QLParity_pow_four
import Mathlib
import Definitions.Def_ChapterParityQL
import Theorems.Thm_BookProof_ChapterParityQL_QLParity_sq
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterParity
open BookProof.ChapterParityQL



open Matrix
open scoped Kronecker


open BookProof.ChapterA3
open BookProof.ChapterParity

set_option maxHeartbeats 1000000 in
theorem solution : QLParity * QLParity * (QLParity * QLParity) = 1 := by

  rw [QLParity_sq]; simp
