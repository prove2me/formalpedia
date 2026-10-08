-- Prove2me | solution 1 for BookProof.ChapterA3q.projSym_add_projAnti_add_projMixed
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:05:09.812465+00:00
-- url     : https://prove2.me/submissions/29f150ff-2fa9-411e-b815-667f75038be6

import Definitions.Def_ChapterA3q
import Mathlib
set_option autoImplicit false
open Matrix
open scoped BigOperators

open BookProof.ChapterA3 BookProof.ChapterA3n BookProof.ChapterA3o BookProof.ChapterA3q

theorem solution (N : ℕ) :
    projSym N + projAnti N + projMixed N = 1 := by
  unfold projMixed; abel

#print axioms solution
