-- Prove2me | solution 1 for BookProof.ChapterPinOmega.qj_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:00:02.252946+00:00
-- url     : https://prove2.me/submissions/7c797db0-f33e-48a8-99bc-b64d8642da71

-- Generated from ChapterPinOmega.lean — solution of BookProof.ChapterPinOmega.qj_sq
import Mathlib
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterPinOmega



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : qj * qj = -1 := by
 decide
