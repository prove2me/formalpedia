-- Prove2me | solution 1 for BookProof.ChapterPinOmega.qj_qk
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:00:08.349592+00:00
-- url     : https://prove2.me/submissions/770bd1bf-fd52-4a8c-909e-a86bd1d1e20c

-- Generated from ChapterPinOmega.lean — solution of BookProof.ChapterPinOmega.qj_qk
import Mathlib
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterPinOmega



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : qj * qk = qi := by
 decide
