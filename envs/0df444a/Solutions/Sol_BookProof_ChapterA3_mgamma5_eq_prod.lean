-- Prove2me | solution 1 for BookProof.ChapterA3.mgamma5_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:58:35.480408+00:00
-- url     : https://prove2.me/submissions/7eb2f04c-ce03-4364-bef7-13c98736b782

-- Generated from ChapterA3.lean — solution of BookProof.ChapterA3.mgamma5_eq_prod
import Mathlib
import Definitions.Def_ChapterA3
import Theorems.Thm_BookProof_ChapterA3_mgamma5Z_eq_prod
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution :
    mgamma5 = mgamma 0 * mgamma 1 * mgamma 2 * mgamma 3 := by

  rw [mgamma5, mgamma, mgamma, mgamma, mgamma, mgamma5Z_eq_prod, map_mul, map_mul, map_mul]
