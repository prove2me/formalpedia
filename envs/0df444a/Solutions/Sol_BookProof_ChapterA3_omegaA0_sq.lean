-- Prove2me | solution 1 for BookProof.ChapterA3.omegaA0_sq
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T15:27:18.138628+00:00
-- url     : https://prove2.me/submissions/a358de79-5679-4a50-8257-ac52207b24df

import Mathlib
import Definitions.Def_ChapterA3d
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3c

open BookProof.ChapterA3
open Matrix

theorem solution : omegaA0 * omegaA0 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [omegaA0, mgammaR, mgammaZ, Matrix.mul_apply, Fin.sum_univ_succ]

#print axioms solution
