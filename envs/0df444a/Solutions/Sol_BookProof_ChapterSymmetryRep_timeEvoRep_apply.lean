-- Prove2me | solution 1 for BookProof.ChapterSymmetryRep.timeEvoRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T20:20:36.185398+00:00
-- url     : https://prove2.me/submissions/13cf991c-773d-45df-a070-0e52fe45e574

-- Generated from ChapterSymmetryRep.lean — solution of BookProof.ChapterSymmetryRep.timeEvoRep_apply
import Mathlib
import Definitions.Def_ChapterSymmetryRep
import Definitions.Def_ChapterConservative
open BookProof.ChapterSymmetryRep



open scoped Matrix


open BookProof.ChapterConservative

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option maxHeartbeats 1000000 in
theorem solution (H : Matrix n n ℂ) (hH : H.IsHermitian) (t : ℝ) :
    (timeEvoRep H hH (Multiplicative.ofAdd t) : Matrix n n ℂ) = timeEvo H t := rfl
