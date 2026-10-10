-- Prove2me | solution 1 for BookProof.ChapterPinOmega.qi_qj_qk
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:00:15.495424+00:00
-- url     : https://prove2.me/submissions/7c92ed7a-6c52-4e65-8ccc-c75c7cac0e8c

-- Generated from ChapterPinOmega.lean — solution of BookProof.ChapterPinOmega.qi_qj_qk
import Mathlib
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterPinOmega



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : qi * qj * qk = -1 := by
 decide
