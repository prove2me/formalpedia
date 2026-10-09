-- Prove2me | solution 1 for BookProof.ChapterA3.mgamma5_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:58:47.418565+00:00
-- url     : https://prove2.me/submissions/6547216a-f510-4745-acc6-f228ff5953e4

-- Generated from ChapterA3.lean — solution of BookProof.ChapterA3.mgamma5_sq
import Mathlib
import Definitions.Def_ChapterA3
import Theorems.Thm_BookProof_ChapterA3_mgamma5Z_sq
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution :
    mgamma5 * mgamma5 = -(1 : Matrix (Fin 4) (Fin 4) ℂ) := by

  rw [mgamma5, ← map_mul, mgamma5Z_sq, map_neg, map_one]
