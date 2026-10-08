-- Prove2me | solution 1 for BookProof.ChapterA3.castMat_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T15:21:32.872889+00:00
-- url     : https://prove2.me/submissions/a1369c2f-6af9-47c3-a859-821510bfce86

import Mathlib
import Definitions.Def_ChapterA3d
import Definitions.Def_ChapterA3

open BookProof.ChapterA3
open Matrix

theorem solution :
    (Int.castRingHom ℝ).mapMatrix (-1 : Matrix (Fin 4) (Fin 4) ℤ) = -1 := by
  ext i j
  simp [Matrix.one_apply]

#print axioms solution
