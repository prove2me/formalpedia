-- Prove2me | solution 1 for BookProof.ChapterSE2.se2_coef_22
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:03:54.176441+00:00
-- url     : https://prove2.me/submissions/953771de-21ae-48f4-8cde-a77aa593c679

-- Generated from ChapterSE2.lean — solution of BookProof.ChapterSE2.se2_coef_22
import Mathlib
import Definitions.Def_ChapterSE2
import Definitions.Def_ChapterA3
open BookProof.ChapterSE2



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution :
    mgamma5Z * mgammaZ 2 * (mgammaZ 0 + mgammaZ 3) *
      (mgamma5Z * mgammaZ 2 * (mgammaZ 0 + mgammaZ 3)) = 0 := by
 decide
