-- Prove2me | solution 1 for BookProof.ChapterSE2.se2_coef_11
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:03:51.259987+00:00
-- url     : https://prove2.me/submissions/3c1b1d2f-9a4a-4179-ad15-6ca595fb3b78

-- Generated from ChapterSE2.lean — solution of BookProof.ChapterSE2.se2_coef_11
import Mathlib
import Definitions.Def_ChapterSE2
import Definitions.Def_ChapterA3
open BookProof.ChapterSE2



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution :
    mgamma5Z * mgammaZ 1 * (mgammaZ 0 + mgammaZ 3) *
      (mgamma5Z * mgammaZ 1 * (mgammaZ 0 + mgammaZ 3)) = 0 := by
 decide
