-- Prove2me | solution 1 for BookProof.ChapterA3.omegaG05_sq
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T15:27:38.894985+00:00
-- url     : https://prove2.me/submissions/eb20f288-cb3e-4506-9bdb-122fa984466a

import Mathlib
import Definitions.Def_ChapterA3d
import Definitions.Def_ChapterA3

open BookProof.ChapterA3
open Matrix

theorem solution : omegaG05 * omegaG05 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [omegaG05, omegaG05Z, mgammaZ, mgamma5Z, Matrix.mul_apply,
      Fin.sum_univ_succ]

#print axioms solution
