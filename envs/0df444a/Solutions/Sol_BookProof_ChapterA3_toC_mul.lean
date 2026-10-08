-- Prove2me | solution 1 for BookProof.ChapterA3.toC_mul
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T16:21:48.794985+00:00
-- url     : https://prove2.me/submissions/9767648a-5052-4efa-98c3-2c391cc58a07

import Mathlib
import Definitions.Def_ChapterA3b
import Definitions.Def_ChapterA3

open BookProof.ChapterA3
open Matrix

theorem solution (M N : Matrix (Fin 4) (Fin 4) ℝ) : toC (M * N) = toC M * toC N := by
  ext i j
  simp [toC, Matrix.mul_apply]

#print axioms solution
