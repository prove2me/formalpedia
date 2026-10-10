-- Prove2me | solution 1 for BookProof.ChapterA3.mgammaZ_transpose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:35:57.897766+00:00
-- url     : https://prove2.me/submissions/5146e910-aa39-4aab-98d0-6c5466843149

-- Generated from ChapterPauliCommutant.lean — solution of BookProof.ChapterA3.mgammaZ_transpose
import Mathlib
import Definitions.Def_ChapterPauliCommutant
import Definitions.Def_ChapterA3
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution (μ : Fin 4) :
    (mgammaZ μ)ᵀ = (if μ = 0 then (-1 : ℤ) else 1) • mgammaZ μ := by
 revert μ; decide
