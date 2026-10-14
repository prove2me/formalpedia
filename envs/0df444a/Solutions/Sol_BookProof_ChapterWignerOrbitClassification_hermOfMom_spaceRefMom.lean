-- Prove2me | solution 1 for BookProof.ChapterWignerOrbitClassification.hermOfMom_spaceRefMom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:51:45.193989+00:00
-- url     : https://prove2.me/submissions/b9e980d6-835b-484e-85f8-c0b5f06e905d

-- Generated from ChapterWignerOrbitClassification.lean — solution of BookProof.ChapterWignerOrbitClassification.hermOfMom_spaceRefMom
import Mathlib
import Definitions.Def_ChapterWignerOrbitClassification
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerOrbitClassification



open Matrix Complex


open BookProof.ChapterWignerLittleGroup BookProof.ChapterWignerLittleGroupOrbits

set_option maxHeartbeats 1000000 in
theorem solution (m : ℝ) :
    hermOfMom (spaceRefMom m) = !![(m : ℂ), 0; 0, -(m : ℂ)] := by

  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermOfMom, spaceRefMom]
