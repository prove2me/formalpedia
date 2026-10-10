-- Prove2me | solution 1 for BookProof.ChapterPinOmega.qjC_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:00:28.202678+00:00
-- url     : https://prove2.me/submissions/b2c180cf-d4b5-4289-8af2-65bdf895cb48

-- Generated from ChapterPinOmega.lean — solution of BookProof.ChapterPinOmega.qjC_sq
import Mathlib
import Definitions.Def_ChapterPinOmega
import Theorems.Thm_BookProof_ChapterPinOmega_qj_sq
import Theorems.Thm_BookProof_ChapterPinOmega_qjC_eq_cast
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterPinOmega



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : qjC * qjC = -1 := by

  rw [qjC_eq_cast, ← map_mul, qj_sq, map_neg, map_one]
