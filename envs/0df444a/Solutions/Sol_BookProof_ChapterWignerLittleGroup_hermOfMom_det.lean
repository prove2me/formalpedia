-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroup.hermOfMom_det
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:59:56.278782+00:00
-- url     : https://prove2.me/submissions/9252015f-4bfd-43b5-8c4b-1c67945eb8a9

-- Generated from ChapterWignerLittleGroup.lean — solution of BookProof.ChapterWignerLittleGroup.hermOfMom_det
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup



open Matrix Complex

set_option maxHeartbeats 1000000 in
theorem solution (p : Fin 4 → ℝ) :
    (hermOfMom p).det = ((p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 : ℝ) : ℂ) := by

  simp only [hermOfMom, Matrix.det_fin_two_of]
  push_cast
  ring_nf
  simp [Complex.I_sq]
  ring
