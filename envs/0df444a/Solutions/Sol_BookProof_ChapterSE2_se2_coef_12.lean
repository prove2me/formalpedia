-- Prove2me | solution 1 for BookProof.ChapterSE2.se2_coef_12
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:03:52.17568+00:00
-- url     : https://prove2.me/submissions/4d34f94b-4c6e-4566-b4ac-ed158deaf8de

-- Generated from ChapterSE2.lean — solution of BookProof.ChapterSE2.se2_coef_12
import Mathlib
import Definitions.Def_ChapterSE2
import Definitions.Def_ChapterA3
open BookProof.ChapterSE2



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution :
    mgamma5Z * mgammaZ 1 * (mgammaZ 0 + mgammaZ 3) *
      (mgamma5Z * mgammaZ 2 * (mgammaZ 0 + mgammaZ 3)) = 0 := by
 decide
