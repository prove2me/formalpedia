-- Prove2me | solution 1 for BookProof.ChapterSoftmaxBorn.bornDenom_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:37:12.71158+00:00
-- url     : https://prove2.me/submissions/8c9fc665-0b58-4239-8255-a5502170d6ec

-- Generated from ChapterSoftmaxBorn.lean — solution of BookProof.ChapterSoftmaxBorn.bornDenom_pos
import Mathlib
import Definitions.Def_ChapterSoftmaxBorn
import Theorems.Thm_BookProof_ChapterSoftmaxBorn_bornNumer_pos
import Definitions.Def_ChapterCoherentOverlap
open BookProof.ChapterSoftmaxBorn



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n))
    (j : Fin m) : 0 < ∑ i, bornNumer q (k i) := Finset.sum_pos (fun l _ => bornNumer_pos q (k l)) ⟨j, Finset.mem_univ j⟩
