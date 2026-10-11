-- Prove2me | solution 1 for BookProof.ChapterWignerLittleGroup.act_det_of_sl
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:00:04.432992+00:00
-- url     : https://prove2.me/submissions/3b288d57-f93a-43ed-bcf2-ec767a5e2459

-- Generated from ChapterWignerLittleGroup.lean — solution of BookProof.ChapterWignerLittleGroup.act_det_of_sl
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
import Theorems.Thm_BookProof_ChapterWignerLittleGroup_act_det
open BookProof.ChapterWignerLittleGroup



open Matrix Complex

set_option maxHeartbeats 1000000 in
theorem solution (A X : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) :
    (act A X).det = X.det := by

  rw [act_det, hA]; simp
