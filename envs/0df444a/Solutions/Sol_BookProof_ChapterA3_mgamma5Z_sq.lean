-- Prove2me | solution 1 for BookProof.ChapterA3.mgamma5Z_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:58:08.373314+00:00
-- url     : https://prove2.me/submissions/7c2dd74c-4f69-47ae-b6e5-3b3f37f100e9

-- Generated from ChapterA3.lean — solution of BookProof.ChapterA3.mgamma5Z_sq
import Mathlib
import Definitions.Def_ChapterA3
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : mgamma5Z * mgamma5Z = -1 := by
 decide
