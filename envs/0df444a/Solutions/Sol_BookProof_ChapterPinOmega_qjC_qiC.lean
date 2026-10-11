-- Prove2me | solution 1 for BookProof.ChapterPinOmega.qjC_qiC
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:04:54.557083+00:00
-- url     : https://prove2.me/submissions/15fcf2e4-0a45-47f1-adbd-30698cc50d24

-- Generated from ChapterPinOmega.lean — solution of BookProof.ChapterPinOmega.qjC_qiC
import Mathlib
import Definitions.Def_ChapterPinOmega
import Theorems.Thm_BookProof_ChapterPinOmega_qj_qi
import Theorems.Thm_BookProof_ChapterPinOmega_qiC_eq_cast
import Theorems.Thm_BookProof_ChapterPinOmega_qjC_eq_cast
import Theorems.Thm_BookProof_ChapterPinOmega_qkC_eq_cast
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterPinOmega



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : qjC * qiC = -qkC := by

  rw [qiC_eq_cast, qjC_eq_cast, qkC_eq_cast, ← map_mul, qj_qi, map_neg]
