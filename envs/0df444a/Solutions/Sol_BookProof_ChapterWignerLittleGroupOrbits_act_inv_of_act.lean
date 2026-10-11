-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroupOrbits.act_inv_of_act
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:00:39.872353+00:00
-- url     : https://prove2.me/submissions/aa87918a-57fa-4c9f-bcee-8f5f81d118e6

-- Generated from ChapterWignerLittleGroupOrbits.lean — solution of BookProof.ChapterWignerLittleGroupOrbits.act_inv_of_act
import Mathlib
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_act_mul
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_act_one
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroupOrbits



open Matrix Complex
open scoped ComplexOrder


open BookProof.ChapterWignerLittleGroup

set_option maxHeartbeats 1000000 in
theorem solution {A X Y : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) (h : act A X = Y) :
    act A⁻¹ Y = X := by

  have hunit : IsUnit A.det := by rw [hA]; exact isUnit_one
  rw [← h, ← act_mul, Matrix.nonsing_inv_mul A hunit, act_one]
