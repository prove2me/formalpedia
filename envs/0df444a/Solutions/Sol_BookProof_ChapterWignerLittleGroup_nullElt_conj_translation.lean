-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroup.nullElt_conj_translation
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:00:24.817059+00:00
-- url     : https://prove2.me/submissions/e2d3a8f2-007d-43c6-9b3c-8ef37be40698

-- Generated from ChapterWignerLittleGroup.lean — solution of BookProof.ChapterWignerLittleGroup.nullElt_conj_translation
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_nullElt_mul
open BookProof.ChapterWignerLittleGroup



open Matrix Complex

set_option maxHeartbeats 1000000 in
theorem solution (a b : ℂ) (ha : a * (starRingEnd ℂ) a = 1) :
    nullElt a 0 * nullElt 1 b * nullElt ((starRingEnd ℂ) a) 0 = nullElt 1 (a * a * b) := by

  have h : (starRingEnd ℂ) ((starRingEnd ℂ) a) = a := by simp
  rw [nullElt_mul, nullElt_mul, h]
  simp only [nullElt]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha, mul_comm, mul_left_comm]
