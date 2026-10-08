-- Prove2me | solution 1 for BookProof.ChapterA3x.projSym_add_projAnti_add_projMixed
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:56:15.288996+00:00
-- url     : https://prove2.me/submissions/601a1e11-df97-425f-9c92-cb800818c152

-- Generated from ChapterA3x.lean — theorem BookProof.ChapterA3x.projSym_add_projAnti_add_projMixed
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3p
import Mathlib
import Definitions.Def_ChapterA3x
import Definitions.Def_ChapterA3l
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterA3o
open BookProof.ChapterA3n
open BookProof.ChapterA3o
open BookProof.ChapterA3x


open Matrix
open scoped BigOperators


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o
open BookProof.ChapterA3p

theorem solution (N : ℕ) :
    projSym N + projAnti N + projMixed N = 1 := by
  simp [projMixed]

#print axioms solution
