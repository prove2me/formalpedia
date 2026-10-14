-- Prove2me | solution 1 for BookProof.ChapterSoftmaxBorn.softmax_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T17:19:06.001289+00:00
-- url     : https://prove2.me/submissions/4674d1fc-562a-494e-a5d4-195d08712129

-- Generated from ChapterSoftmaxBorn.lean — solution of BookProof.ChapterSoftmaxBorn.softmax_pos
import Mathlib
import Definitions.Def_ChapterSoftmaxBorn
import Theorems.Thm_BookProof_ChapterSoftmaxBorn_softmaxDenom_pos
import Definitions.Def_ChapterCoherentOverlap
open BookProof.ChapterSoftmaxBorn



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : 0 < softmax beta q k j := div_pos (Real.exp_pos _) (softmaxDenom_pos beta q k j)
