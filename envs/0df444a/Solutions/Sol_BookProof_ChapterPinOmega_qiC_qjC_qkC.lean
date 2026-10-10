-- Prove2me | solution 1 for BookProof.ChapterPinOmega.qiC_qjC_qkC
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:00:34.431106+00:00
-- url     : https://prove2.me/submissions/f85db874-866f-41bc-9738-d40931be1a35

-- Generated from ChapterPinOmega.lean — solution of BookProof.ChapterPinOmega.qiC_qjC_qkC
import Mathlib
import Definitions.Def_ChapterPinOmega
import Theorems.Thm_BookProof_ChapterPinOmega_qi_qj_qk
import Theorems.Thm_BookProof_ChapterPinOmega_qiC_eq_cast
import Theorems.Thm_BookProof_ChapterPinOmega_qjC_eq_cast
import Theorems.Thm_BookProof_ChapterPinOmega_qkC_eq_cast
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterPinOmega



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : qiC * qjC * qkC = -1 := by

  rw [qiC_eq_cast, qjC_eq_cast, qkC_eq_cast, ← map_mul, ← map_mul, qi_qj_qk,
    map_neg, map_one]
