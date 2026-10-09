-- Prove2me | solution 1 for BookProof.ChapterA3.mgammaZ_transpose_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:57:00.522913+00:00
-- url     : https://prove2.me/submissions/98a4de5e-4c5e-4cc8-b71a-c1f36653f933

-- Generated from ChapterA3.lean — solution of BookProof.ChapterA3.mgammaZ_transpose_mul
import Mathlib
import Definitions.Def_ChapterA3
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution (μ : Fin 4) : (mgammaZ μ)ᵀ * mgammaZ μ = 1 := by

  revert μ; decide
