-- Prove2me | solution 1 for BookProof.ChapterWignerOrbitClassification.negMom_negMom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:53:40.644636+00:00
-- url     : https://prove2.me/submissions/a7443050-3478-45b9-b724-97ccf381890b

-- Generated from ChapterWignerOrbitClassification.lean — solution of BookProof.ChapterWignerOrbitClassification.negMom_negMom
import Mathlib
import Definitions.Def_ChapterWignerOrbitClassification
import Definitions.Def_ChapterWignerLittleGroup
import Definitions.Def_ChapterWignerLittleGroupOrbits
open BookProof.ChapterWignerOrbitClassification



open Matrix Complex


open BookProof.ChapterWignerLittleGroup BookProof.ChapterWignerLittleGroupOrbits

set_option maxHeartbeats 1000000 in
theorem solution (p : Fin 4 → ℝ) : negMom (negMom p) = p := by

  funext i; simp [negMom]
