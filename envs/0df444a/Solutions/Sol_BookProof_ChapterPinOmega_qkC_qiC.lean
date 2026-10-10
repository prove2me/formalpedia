-- Prove2me | solution 1 for BookProof.ChapterPinOmega.qkC_qiC
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:00:33.310572+00:00
-- url     : https://prove2.me/submissions/2912bfd2-7884-4652-86d6-0c04b9201537

-- Generated from ChapterPinOmega.lean — solution of BookProof.ChapterPinOmega.qkC_qiC
import Mathlib
import Definitions.Def_ChapterPinOmega
import Theorems.Thm_BookProof_ChapterPinOmega_qk_qi
import Theorems.Thm_BookProof_ChapterPinOmega_qiC_eq_cast
import Theorems.Thm_BookProof_ChapterPinOmega_qjC_eq_cast
import Theorems.Thm_BookProof_ChapterPinOmega_qkC_eq_cast
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterPinOmega



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : qkC * qiC = qjC := by

  rw [qiC_eq_cast, qjC_eq_cast, qkC_eq_cast, ← map_mul, qk_qi]
