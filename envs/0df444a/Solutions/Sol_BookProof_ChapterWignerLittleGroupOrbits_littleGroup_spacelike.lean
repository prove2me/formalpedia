-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroupOrbits.littleGroup_spacelike
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:51:39.922039+00:00
-- url     : https://prove2.me/submissions/f0981f39-a352-4fc2-9ac0-84b6b2605f1c

-- Generated from ChapterWignerLittleGroupOrbits.lean — solution of BookProof.ChapterWignerLittleGroupOrbits.littleGroup_spacelike
import Mathlib
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Theorems.Thm_BookProof_ChapterWignerLittleGroupOrbits_hermOfMom_spaceMom
import Definitions.Def_ChapterLittleGroup
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroupOrbits



open Matrix Complex
open scoped ComplexOrder


open BookProof.ChapterWignerLittleGroup

set_option maxHeartbeats 1000000 in
theorem solution : littleGroup spaceMom = SU11 := by

  ext A
  simp [littleGroup, SU11, act, hermOfMom_spaceMom]
