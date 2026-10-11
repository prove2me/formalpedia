-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroupOrbits.det_inv_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:00:41.185624+00:00
-- url     : https://prove2.me/submissions/4fe65710-0e71-40fe-88c4-8880f822eaf3

-- Generated from ChapterWignerLittleGroupOrbits.lean — solution of BookProof.ChapterWignerLittleGroupOrbits.det_inv_eq_one
import Mathlib
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroupOrbits



open Matrix Complex
open scoped ComplexOrder


open BookProof.ChapterWignerLittleGroup

set_option maxHeartbeats 1000000 in
theorem solution {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) : (A⁻¹).det = 1 := by

  rw [Matrix.det_nonsing_inv, hA]
  simp
