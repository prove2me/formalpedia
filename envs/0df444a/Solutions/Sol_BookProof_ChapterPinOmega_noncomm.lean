-- Prove2me | solution 1 for BookProof.ChapterPinOmega.noncomm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:00:16.714309+00:00
-- url     : https://prove2.me/submissions/ddba2688-00f6-4730-8fd2-d830f66b09f1

-- Generated from ChapterPinOmega.lean — solution of BookProof.ChapterPinOmega.noncomm
import Mathlib
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterPinOmega



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : qi * qj ≠ qj * qi := by
 decide
