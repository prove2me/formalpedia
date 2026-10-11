-- Prove2me | solution 1 for BookProof.ChapterSE2.se2_coef_21
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:03:53.240196+00:00
-- url     : https://prove2.me/submissions/7fcc6931-11b9-4c85-af82-8f8dfbe829d5

-- Generated from ChapterSE2.lean — solution of BookProof.ChapterSE2.se2_coef_21
import Mathlib
import Definitions.Def_ChapterSE2
import Definitions.Def_ChapterA3
open BookProof.ChapterSE2



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution :
    mgamma5Z * mgammaZ 2 * (mgammaZ 0 + mgammaZ 3) *
      (mgamma5Z * mgammaZ 1 * (mgammaZ 0 + mgammaZ 3)) = 0 := by
 decide
