-- Prove2me | solution 1 for BookProof.ChapterA3.det_sq_of_sq_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:05:10.944335+00:00
-- url     : https://prove2.me/submissions/ce22a44d-ba19-4077-a3ea-8db3b6fe859a

import Mathlib
import Definitions.Def_ChapterA3d
open BookProof.ChapterA3 Matrix

theorem solution {S : Matrix (Fin 4) (Fin 4) ℝ} (h : S * S = -1) :
    S.det * S.det = 1 := by
  have hd := congrArg Matrix.det h
  norm_num [Matrix.det_mul, Matrix.det_neg] at hd
  exact hd

#print axioms solution
