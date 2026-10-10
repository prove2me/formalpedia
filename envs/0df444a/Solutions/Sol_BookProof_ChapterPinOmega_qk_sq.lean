-- Prove2me | solution 1 for BookProof.ChapterPinOmega.qk_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:00:04.874987+00:00
-- url     : https://prove2.me/submissions/9af98f20-47f4-4774-95cb-b6c3d29f04ba

-- Generated from ChapterPinOmega.lean — solution of BookProof.ChapterPinOmega.qk_sq
import Mathlib
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterPinOmega



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : qk * qk = -1 := by
 decide
