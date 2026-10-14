-- Prove2me | solution 1 for BookProof.ChapterSoftmaxBorn.softmaxDenom_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T17:17:25.400591+00:00
-- url     : https://prove2.me/submissions/a3690377-6f26-4143-afe0-5945cfb7c0f5

-- Generated from ChapterSoftmaxBorn.lean — solution of BookProof.ChapterSoftmaxBorn.softmaxDenom_pos
import Mathlib
import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterCoherentOverlap
open BookProof.ChapterSoftmaxBorn



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) :
    0 < ∑ l, Real.exp (beta * inner ℝ q (k l)) := Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨j, Finset.mem_univ j⟩
