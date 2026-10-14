-- Prove2me | solution 1 for BookProof.ChapterSoftmaxBorn.bornWeight_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T17:17:26.53399+00:00
-- url     : https://prove2.me/submissions/87e5524c-de4e-4704-8dee-79325c2f924e

-- Generated from ChapterSoftmaxBorn.lean — solution of BookProof.ChapterSoftmaxBorn.bornWeight_pos
import Mathlib
import Definitions.Def_ChapterSoftmaxBorn
import Theorems.Thm_BookProof_ChapterSoftmaxBorn_bornNumer_pos
import Theorems.Thm_BookProof_ChapterSoftmaxBorn_bornDenom_pos
import Definitions.Def_ChapterCoherentOverlap
open BookProof.ChapterSoftmaxBorn



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n))
    (j : Fin m) : 0 < bornWeight q k j := div_pos (bornNumer_pos q (k j)) (bornDenom_pos q k j)
