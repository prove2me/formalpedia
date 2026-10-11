-- Prove2me | solution 1 for BookProof.ChapterSE2.Nmat_inv
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:03:55.273979+00:00
-- url     : https://prove2.me/submissions/56bb0523-a007-4a5a-80f4-22124b2477d5

-- Generated from ChapterSE2.lean — solution of BookProof.ChapterSE2.Nmat_inv
import Mathlib
import Definitions.Def_ChapterSE2
import Definitions.Def_ChapterA3
open BookProof.ChapterSE2



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution (a b : ℝ) : Nmat a b * Nmat (-a) (-b) = 1 := by

  convert Nmat_mul a b ( -a ) ( -b ) using 1;
  norm_num [ Nmat_zero ]
