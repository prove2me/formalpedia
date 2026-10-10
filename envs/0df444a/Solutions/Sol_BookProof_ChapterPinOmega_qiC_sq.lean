-- Prove2me | solution 1 for BookProof.ChapterPinOmega.qiC_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:00:27.110397+00:00
-- url     : https://prove2.me/submissions/68bb90c4-493c-4f9f-8b9f-cce91f754879

-- Generated from ChapterPinOmega.lean — solution of BookProof.ChapterPinOmega.qiC_sq
import Mathlib
import Definitions.Def_ChapterPinOmega
import Theorems.Thm_BookProof_ChapterPinOmega_qi_sq
import Theorems.Thm_BookProof_ChapterPinOmega_qiC_eq_cast
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterPinOmega



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : qiC * qiC = -1 := by

  rw [qiC_eq_cast, ← map_mul, qi_sq, map_neg, map_one]
