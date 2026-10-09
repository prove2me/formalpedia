-- Prove2me | solution 1 for BookProof.ChapterA3l.projSym_add_projAsym
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:38:51.907047+00:00
-- url     : https://prove2.me/submissions/c8e3acff-331b-4d91-9349-a826070b13fa

-- Generated from ChapterA3l.lean — solution of BookProof.ChapterA3l.projSym_add_projAsym
import Mathlib
import Definitions.Def_ChapterA3l
open BookProof.ChapterA3l



open Matrix
open scoped Kronecker


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k

set_option maxHeartbeats 1000000 in
theorem solution : projSym + projAsym = 1 := by

  unfold projSym projAsym
  module
