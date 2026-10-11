-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroup.act_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:00:07.645528+00:00
-- url     : https://prove2.me/submissions/8f7d377f-d406-45b5-bfd4-95d1f078d819

-- Generated from ChapterWignerLittleGroup.lean — solution of BookProof.ChapterWignerLittleGroup.act_one
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup



open Matrix Complex

set_option maxHeartbeats 1000000 in
theorem solution (X : Matrix (Fin 2) (Fin 2) ℂ) : act 1 X = X := by

  simp [act]
