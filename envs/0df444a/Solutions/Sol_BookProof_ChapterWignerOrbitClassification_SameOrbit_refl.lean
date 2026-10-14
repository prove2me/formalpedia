-- Prove2me | solution 1 for BookProof.ChapterWignerOrbitClassification.SameOrbit.refl
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:51:40.974016+00:00
-- url     : https://prove2.me/submissions/4755e1ed-af59-41ad-8ed4-2b4b8d4532ec

-- Generated from ChapterWignerOrbitClassification.lean — solution of BookProof.ChapterWignerOrbitClassification.SameOrbit.refl
import Mathlib
import Definitions.Def_ChapterWignerOrbitClassification
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_act_one
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerOrbitClassification



open Matrix Complex


open BookProof.ChapterWignerLittleGroup BookProof.ChapterWignerLittleGroupOrbits

set_option maxHeartbeats 1000000 in
theorem solution (p : Fin 4 → ℝ) : SameOrbit p p := ⟨1, by simp, act_one _⟩
