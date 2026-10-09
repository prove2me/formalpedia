-- Prove2me | solution 1 for BookProof.ChapterA3.mgamma5_anticomm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:58:59.53522+00:00
-- url     : https://prove2.me/submissions/18fde79b-70eb-4bd5-b705-74f06375dca3

-- Generated from ChapterA3.lean — solution of BookProof.ChapterA3.mgamma5_anticomm
import Mathlib
import Definitions.Def_ChapterA3
import Theorems.Thm_BookProof_ChapterA3_mgamma5Z_anticomm
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution (μ : Fin 4) :
    mgamma5 * mgamma μ + mgamma μ * mgamma5 = 0 := by

  rw [mgamma5, mgamma, ← map_mul, ← map_mul, ← map_add, mgamma5Z_anticomm, map_zero]
