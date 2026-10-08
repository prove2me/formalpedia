-- Prove2me | solution 1 for BookProof.ChapterA3j.chir_sq
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T15:24:42.077514+00:00
-- url     : https://prove2.me/submissions/a02d4583-2051-43a8-8f50-48da67efd89a

import Mathlib
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3

open Matrix
open BookProof.ChapterA3
open BookProof.ChapterA3j

theorem solution : chir * chir = -1 := by
  have hz : BookProof.ChapterA3.mgamma5Z *
      BookProof.ChapterA3.mgamma5Z = -1 := by
    decide
  change ((Int.castRingHom ℂ).mapMatrix BookProof.ChapterA3.mgamma5Z) *
      ((Int.castRingHom ℂ).mapMatrix BookProof.ChapterA3.mgamma5Z) = -1
  rw [← map_mul, hz]
  ext i j
  simp [Matrix.one_apply]

#print axioms solution
