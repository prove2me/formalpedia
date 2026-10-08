-- Prove2me | solution 1 for BookProof.ChapterA4g.SEtwo_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T04:29:50.981491+00:00
-- url     : https://prove2.me/submissions/2ab16b92-1735-4e65-84e4-2900f495a899

import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA4d

open BookProof.ChapterA3 Matrix Complex

theorem solution : (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ SEtwo := by
  simp [SEtwo, det_one, one_apply, normSq_one]
