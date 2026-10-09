-- Prove2me | solution 1 for BookProof.ChapterA3.spinRot_hasAdLambda
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:06:17.093996+00:00
-- url     : https://prove2.me/submissions/784b66be-deb6-4820-9508-d309a71d54f1

-- Generated from ChapterA3e.lean — solution of BookProof.ChapterA3.spinRot_hasAdLambda
import Mathlib
import Definitions.Def_ChapterA3e
import Theorems.Thm_BookProof_ChapterA3_hasAdLambda_of_intModel
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution (j : Fin 3) : HasAdLambda (spinRot j) (adRot j) := by

  have hconj : ∀ μ, spinRotZ j * mgammaZ μ - mgammaZ μ * spinRotZ j
      = ∑ ν, (adRotZ j) μ ν • mgammaZ ν := by
    fin_cases j <;> decide
  exact hasAdLambda_of_intModel (spinRotZ j) (adRotZ j) hconj
