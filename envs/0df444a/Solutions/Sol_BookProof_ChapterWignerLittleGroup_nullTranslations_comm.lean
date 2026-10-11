-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroup.nullTranslations_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:00:23.425827+00:00
-- url     : https://prove2.me/submissions/626582c0-1cac-43f8-88e7-1cd33fad2a67

-- Generated from ChapterWignerLittleGroup.lean — solution of BookProof.ChapterWignerLittleGroup.nullTranslations_comm
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_nullTranslations_mul
open BookProof.ChapterWignerLittleGroup



open Matrix Complex

set_option maxHeartbeats 1000000 in
theorem solution (b b' : ℂ) :
    nullElt 1 b * nullElt 1 b' = nullElt 1 b' * nullElt 1 b := by

  rw [nullTranslations_mul, nullTranslations_mul, add_comm b' b]
