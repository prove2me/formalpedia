-- Prove2me | solution 1 for BookProof.ChapterSoftmaxBorn.bornWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T17:19:04.172485+00:00
-- url     : https://prove2.me/submissions/ce82241f-1e90-4f12-a0d4-f17217f5ca42

-- Generated from ChapterSoftmaxBorn.lean — solution of BookProof.ChapterSoftmaxBorn.bornWeight_nonneg
import Mathlib
import Definitions.Def_ChapterSoftmaxBorn
import Theorems.Thm_BookProof_ChapterSoftmaxBorn_bornWeight_pos
import Definitions.Def_ChapterCoherentOverlap
open BookProof.ChapterSoftmaxBorn



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n))
    (j : Fin m) : 0 ≤ bornWeight q k j := le_of_lt (bornWeight_pos q k j)
