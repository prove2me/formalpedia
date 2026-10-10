-- Prove2me | solution 1 for BookProof.ChapterPinOmega.qkC_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:00:29.596997+00:00
-- url     : https://prove2.me/submissions/2c438fdd-0b5d-470a-9ad3-33391ce7839e

-- Generated from ChapterPinOmega.lean — solution of BookProof.ChapterPinOmega.qkC_sq
import Mathlib
import Definitions.Def_ChapterPinOmega
import Theorems.Thm_BookProof_ChapterPinOmega_qk_sq
import Theorems.Thm_BookProof_ChapterPinOmega_qkC_eq_cast
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterPinOmega



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : qkC * qkC = -1 := by

  rw [qkC_eq_cast, ← map_mul, qk_sq, map_neg, map_one]
