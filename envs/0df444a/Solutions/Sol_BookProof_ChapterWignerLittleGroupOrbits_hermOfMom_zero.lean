-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroupOrbits.hermOfMom_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:00:34.885934+00:00
-- url     : https://prove2.me/submissions/13804d80-7205-4fab-b246-e19d2fae63e0

-- Generated from ChapterWignerLittleGroupOrbits.lean — solution of BookProof.ChapterWignerLittleGroupOrbits.hermOfMom_zero
import Mathlib
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroupOrbits



open Matrix Complex
open scoped ComplexOrder


open BookProof.ChapterWignerLittleGroup

set_option maxHeartbeats 1000000 in
theorem solution : hermOfMom (fun _ => 0) = 0 := by

  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermOfMom]
