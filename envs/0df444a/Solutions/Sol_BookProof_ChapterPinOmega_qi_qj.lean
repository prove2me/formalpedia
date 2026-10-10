-- Prove2me | solution 1 for BookProof.ChapterPinOmega.qi_qj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:00:06.303891+00:00
-- url     : https://prove2.me/submissions/856264f2-3006-4172-bef3-404a22b8ed04

-- Generated from ChapterPinOmega.lean — solution of BookProof.ChapterPinOmega.qi_qj
import Mathlib
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterPinOmega



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : qi * qj = qk := by
 decide
