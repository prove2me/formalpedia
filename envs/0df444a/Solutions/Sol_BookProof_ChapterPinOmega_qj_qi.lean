-- Prove2me | solution 1 for BookProof.ChapterPinOmega.qj_qi
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:00:11.469059+00:00
-- url     : https://prove2.me/submissions/13aef96c-6eb2-4fc0-a97c-c4b7ac331cf3

-- Generated from ChapterPinOmega.lean — solution of BookProof.ChapterPinOmega.qj_qi
import Mathlib
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterPinOmega



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : qj * qi = -qk := by
 decide
