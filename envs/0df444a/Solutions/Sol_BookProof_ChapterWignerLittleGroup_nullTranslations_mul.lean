-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroup.nullTranslations_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:00:22.199309+00:00
-- url     : https://prove2.me/submissions/b02cc4d1-f5f1-453d-9cb1-54f081a35be0

-- Generated from ChapterWignerLittleGroup.lean — solution of BookProof.ChapterWignerLittleGroup.nullTranslations_mul
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_nullElt_mul
open BookProof.ChapterWignerLittleGroup



open Matrix Complex

set_option maxHeartbeats 1000000 in
theorem solution (b b' : ℂ) :
    nullElt 1 b * nullElt 1 b' = nullElt 1 (b + b') := by

  rw [nullElt_mul]; simp [add_comm]
