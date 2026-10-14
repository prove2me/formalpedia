-- Prove2me | solution 1 for BookProof.ChapterWignerOrbitClassification.minkSq_spaceRefMom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:51:46.159244+00:00
-- url     : https://prove2.me/submissions/20c77e54-05bb-4f20-ade9-050c03e86d72

-- Generated from ChapterWignerOrbitClassification.lean — solution of BookProof.ChapterWignerOrbitClassification.minkSq_spaceRefMom
import Mathlib
import Definitions.Def_ChapterWignerOrbitClassification
import Definitions.Def_ChapterWignerLittleGroup
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterWignerOrbitClassification



open Matrix Complex


open BookProof.ChapterWignerLittleGroup BookProof.ChapterWignerLittleGroupOrbits

set_option maxHeartbeats 1000000 in
theorem solution (m : ℝ) : minkSq (spaceRefMom m) = -m ^ 2 := by

  simp [minkSq, spaceRefMom]
