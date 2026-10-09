-- Prove2me | solution 1 for BookProof.ChapterA3.mgamma5Z_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:57:12.73303+00:00
-- url     : https://prove2.me/submissions/f3212b28-979c-4ba6-85e0-2ecd81e3b34a

-- Generated from ChapterA3.lean — solution of BookProof.ChapterA3.mgamma5Z_eq_prod
import Mathlib
import Definitions.Def_ChapterA3
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution :
    mgamma5Z = mgammaZ 0 * mgammaZ 1 * mgammaZ 2 * mgammaZ 3 := by
 decide
