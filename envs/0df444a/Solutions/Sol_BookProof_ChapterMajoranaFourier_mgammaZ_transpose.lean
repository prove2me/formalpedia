-- Prove2me | solution 1 for BookProof.ChapterMajoranaFourier.mgammaZ_transpose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:41:13.127547+00:00
-- url     : https://prove2.me/submissions/e005f02f-e107-4763-a2ef-4e656d64d694

-- Generated from ChapterMajoranaFourier.lean — solution of BookProof.ChapterMajoranaFourier.mgammaZ_transpose
import Mathlib
import Definitions.Def_ChapterMajoranaFourier
import Definitions.Def_ChapterA3
open BookProof.ChapterMajoranaFourier



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution (μ : Fin 4) :
    (mgammaZ μ)ᵀ = if μ = 0 then -mgammaZ μ else mgammaZ μ := by

  revert μ; decide
