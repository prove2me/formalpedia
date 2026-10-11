-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroupOrbits.hermOfMom_spaceMom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:00:44.060911+00:00
-- url     : https://prove2.me/submissions/17767f66-d054-4e22-9c90-93997173ef53

-- Generated from ChapterWignerLittleGroupOrbits.lean — solution of BookProof.ChapterWignerLittleGroupOrbits.hermOfMom_spaceMom
import Mathlib
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroupOrbits



open Matrix Complex
open scoped ComplexOrder


open BookProof.ChapterWignerLittleGroup

set_option maxHeartbeats 1000000 in
theorem solution : hermOfMom spaceMom = !![(1 : ℂ), 0; 0, -1] := by

  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermOfMom, spaceMom]
