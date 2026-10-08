-- Prove2me | solution 1 for BookProof.ChapterA3u.trace_decomposition_five
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:32:22.6903+00:00
-- url     : https://prove2.me/submissions/7cda73f8-09c6-4f61-9281-4a7c0f958ab0

-- Generated from ChapterA3u.lean — theorem BookProof.ChapterA3u.trace_decomposition_five
import Definitions.Def_ChapterA3q
import Definitions.Def_ChapterA3r
import Mathlib
import Definitions.Def_ChapterA3u
import Definitions.Def_ChapterA3l
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterA3o
open BookProof.ChapterA3l
open BookProof.ChapterA3n
open BookProof.ChapterA3o
open BookProof.ChapterA3u


open Matrix
open scoped BigOperators


open BookProof.ChapterA3n BookProof.ChapterA3o BookProof.ChapterA3q
open BookProof.ChapterA3r

theorem solution :
    Matrix.trace (projSym 5) + Matrix.trace (projAnti 5)
        + Matrix.trace (projMixed 5) = 1024 := by
  rw [projMixed, Matrix.trace_sub, Matrix.trace_sub]
  have hid : Matrix.trace (1 : MN 5) = 1024 := by
    simp [Matrix.trace_one, Idx]
  rw [hid]
  ring

#print axioms solution
