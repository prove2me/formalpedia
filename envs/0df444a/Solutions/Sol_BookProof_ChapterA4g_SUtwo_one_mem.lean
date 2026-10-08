-- Prove2me | solution 1 for BookProof.ChapterA4g.SUtwo_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T04:29:49.911803+00:00
-- url     : https://prove2.me/submissions/bdb69e82-93f7-42ae-ae53-fe4f5e2da7c2

import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA4c

open BookProof.ChapterA3 Matrix

theorem solution : (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ SUtwo := by
  simp [SUtwo, det_one, conjTranspose_one, one_mul]
