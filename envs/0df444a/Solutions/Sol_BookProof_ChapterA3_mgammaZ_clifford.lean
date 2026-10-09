-- Prove2me | solution 1 for BookProof.ChapterA3.mgammaZ_clifford
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:56:59.523979+00:00
-- url     : https://prove2.me/submissions/0dc49556-2014-41fe-b399-a2a2793816dd

-- Generated from ChapterA3.lean — solution of BookProof.ChapterA3.mgammaZ_clifford
import Mathlib
import Definitions.Def_ChapterA3
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution (μ ν : Fin 4) :
    mgammaZ μ * mgammaZ ν + mgammaZ ν * mgammaZ μ =
      (-2 * minkowskiZ μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by

  revert μ ν; decide
