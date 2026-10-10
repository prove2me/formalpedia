-- Prove2me | solution 1 for BookProof.ChapterPinOmega.qk_qj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:00:12.997665+00:00
-- url     : https://prove2.me/submissions/d1f8932a-2b23-4483-8760-3c6db7773db0

-- Generated from ChapterPinOmega.lean — solution of BookProof.ChapterPinOmega.qk_qj
import Mathlib
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterPinOmega



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : qk * qj = -qi := by
 decide
