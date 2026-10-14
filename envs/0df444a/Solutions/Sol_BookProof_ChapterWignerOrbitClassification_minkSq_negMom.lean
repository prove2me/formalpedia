-- Prove2me | solution 1 for BookProof.ChapterWignerOrbitClassification.minkSq_negMom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:53:24.965948+00:00
-- url     : https://prove2.me/submissions/a97de439-3203-487b-844c-b4bf238c1ad6

-- Generated from ChapterWignerOrbitClassification.lean — solution of BookProof.ChapterWignerOrbitClassification.minkSq_negMom
import Mathlib
import Definitions.Def_ChapterWignerOrbitClassification
import Definitions.Def_ChapterWignerLittleGroup
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterWignerOrbitClassification



open Matrix Complex


open BookProof.ChapterWignerLittleGroup BookProof.ChapterWignerLittleGroupOrbits

set_option maxHeartbeats 1000000 in
theorem solution (p : Fin 4 → ℝ) : minkSq (negMom p) = minkSq p := by

  simp [minkSq, negMom]
