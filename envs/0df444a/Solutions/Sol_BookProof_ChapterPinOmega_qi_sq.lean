-- Prove2me | solution 1 for BookProof.ChapterPinOmega.qi_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:00:00.264432+00:00
-- url     : https://prove2.me/submissions/04acc1da-e955-4045-8137-4117a0b4ed24

-- Generated from ChapterPinOmega.lean — solution of BookProof.ChapterPinOmega.qi_sq
import Mathlib
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterPinOmega



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : qi * qi = -1 := by
 decide
