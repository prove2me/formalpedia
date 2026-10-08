-- Prove2me | solution 1 for BookProof.ChapterA3.omegaA5_sq
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T15:27:28.848875+00:00
-- url     : https://prove2.me/submissions/6d28ac62-7215-46ef-a386-42a03b5c1d99

import Mathlib
import Definitions.Def_ChapterA3d
import Definitions.Def_ChapterA3

open BookProof.ChapterA3
open Matrix

theorem solution : omegaA5 * omegaA5 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [omegaA5, omegaA5Z, mgamma5Z, Matrix.mul_apply, Fin.sum_univ_succ]

#print axioms solution
