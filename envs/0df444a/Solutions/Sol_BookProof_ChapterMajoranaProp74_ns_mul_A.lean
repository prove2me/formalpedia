-- Prove2me | solution 1 for BookProof.ChapterMajoranaProp74.ns_mul_A
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:44:29.400995+00:00
-- url     : https://prove2.me/submissions/4cdd3f55-db4a-47bf-b710-6b6ef8164118

-- Generated from ChapterMajoranaProp74.lean — solution of BookProof.ChapterMajoranaProp74.ns_mul_A
import Mathlib
import Definitions.Def_ChapterMajoranaProp74
import Definitions.Def_ChapterMajoranaFourier
import Definitions.Def_ChapterA3
open BookProof.ChapterMajoranaProp74



open Matrix


open BookProof.ChapterMajoranaFourier
open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution {g ns : Matrix (Fin 4) (Fin 4) ℂ} (hns2 : ns * ns = -1) :
    ns * (ns * g) = -g := by

      rw [ ← Matrix.mul_assoc, hns2, neg_one_mul ]
