-- Prove2me | solution 1 for BookProof.ChapterPinOmega.qk_qi
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:00:09.98544+00:00
-- url     : https://prove2.me/submissions/a2bb6225-420c-4aa9-8b14-cfea05417bfc

-- Generated from ChapterPinOmega.lean — solution of BookProof.ChapterPinOmega.qk_qi
import Mathlib
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterPinOmega



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : qk * qi = qj := by
 decide
