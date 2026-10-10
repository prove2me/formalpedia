-- Prove2me | solution 1 for BookProof.ChapterPinOmega.qiC_qjC
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:00:30.792483+00:00
-- url     : https://prove2.me/submissions/d6fa8ebd-3b3c-4685-8c59-eb2f9133d1f5

-- Generated from ChapterPinOmega.lean — solution of BookProof.ChapterPinOmega.qiC_qjC
import Mathlib
import Definitions.Def_ChapterPinOmega
import Theorems.Thm_BookProof_ChapterPinOmega_qi_qj
import Theorems.Thm_BookProof_ChapterPinOmega_qiC_eq_cast
import Theorems.Thm_BookProof_ChapterPinOmega_qjC_eq_cast
import Theorems.Thm_BookProof_ChapterPinOmega_qkC_eq_cast
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterPinOmega



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : qiC * qjC = qkC := by

  rw [qiC_eq_cast, qjC_eq_cast, qkC_eq_cast, ← map_mul, qi_qj]
