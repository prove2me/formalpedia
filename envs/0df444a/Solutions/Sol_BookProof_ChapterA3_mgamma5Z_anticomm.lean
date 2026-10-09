-- Prove2me | solution 1 for BookProof.ChapterA3.mgamma5Z_anticomm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:58:09.352821+00:00
-- url     : https://prove2.me/submissions/1a2a3707-643e-4420-9895-7fca36606cca

-- Generated from ChapterA3.lean — solution of BookProof.ChapterA3.mgamma5Z_anticomm
import Mathlib
import Definitions.Def_ChapterA3
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution (μ : Fin 4) :
    mgamma5Z * mgammaZ μ + mgammaZ μ * mgamma5Z = 0 := by
 revert μ; decide
