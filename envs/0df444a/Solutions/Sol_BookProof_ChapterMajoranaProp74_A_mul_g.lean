-- Prove2me | solution 1 for BookProof.ChapterMajoranaProp74.A_mul_g
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:44:53.938411+00:00
-- url     : https://prove2.me/submissions/26554f31-e6ac-4836-9051-eaa1b729e6f5

-- Generated from ChapterMajoranaProp74.lean — solution of BookProof.ChapterMajoranaProp74.A_mul_g
import Mathlib
import Definitions.Def_ChapterMajoranaProp74
import Definitions.Def_ChapterMajoranaFourier
import Definitions.Def_ChapterA3
open BookProof.ChapterMajoranaProp74



open Matrix


open BookProof.ChapterMajoranaFourier
open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution {g ns : Matrix (Fin 4) (Fin 4) ℂ} (hg2 : g * g = 1) :
    (ns * g) * g = ns := by

      rw [ mul_assoc, hg2, mul_one ]
