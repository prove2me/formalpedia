-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroup.nullElt_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:00:20.987962+00:00
-- url     : https://prove2.me/submissions/bf313a73-0284-4c25-8671-ec2df94c5d35

-- Generated from ChapterWignerLittleGroup.lean — solution of BookProof.ChapterWignerLittleGroup.nullElt_mul
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup



open Matrix Complex

set_option maxHeartbeats 1000000 in
theorem solution (a b a' b' : ℂ) :
    nullElt a b * nullElt a' b' = nullElt (a * a') (a * b' + b * (starRingEnd ℂ) a') := by

  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nullElt, Matrix.mul_apply, Fin.sum_univ_two]
