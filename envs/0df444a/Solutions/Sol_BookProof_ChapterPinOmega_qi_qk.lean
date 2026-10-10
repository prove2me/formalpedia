-- Prove2me | solution 1 for BookProof.ChapterPinOmega.qi_qk
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:00:14.316352+00:00
-- url     : https://prove2.me/submissions/ceb920f8-4c01-40e5-89d9-e899645a1613

-- Generated from ChapterPinOmega.lean — solution of BookProof.ChapterPinOmega.qi_qk
import Mathlib
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterPinOmega



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : qi * qk = -qj := by
 decide
