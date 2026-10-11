-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroup.hermOfMom_restMom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:00:15.027493+00:00
-- url     : https://prove2.me/submissions/7d4318f6-fa4a-4ecc-9481-3e445bcd0a35

-- Generated from ChapterWignerLittleGroup.lean — solution of BookProof.ChapterWignerLittleGroup.hermOfMom_restMom
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup



open Matrix Complex

set_option maxHeartbeats 1000000 in
theorem solution (m : ℝ) :
    hermOfMom (restMom m) = (m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by

  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermOfMom, restMom]
