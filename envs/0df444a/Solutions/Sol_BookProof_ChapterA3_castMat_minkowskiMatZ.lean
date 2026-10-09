-- Prove2me | solution 1 for BookProof.ChapterA3.castMat_minkowskiMatZ
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:03:45.015915+00:00
-- url     : https://prove2.me/submissions/e8b51ff2-04c9-4876-a277-66fc65069f94

-- Generated from ChapterA3e.lean — solution of BookProof.ChapterA3.castMat_minkowskiMatZ
import Mathlib
import Definitions.Def_ChapterA3e
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution :
    (Int.castRingHom ℝ).mapMatrix minkowskiMatZ = minkowskiMat := by

  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, minkowskiMatZ, minkowskiMat,
    minkowskiR]
