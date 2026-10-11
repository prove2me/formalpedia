-- Prove2me | solution 1 for BookProof.ChapterSoftmaxSharpness.softmax_smul_query
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:43:42.824331+00:00
-- url     : https://prove2.me/submissions/6538d5c0-02a9-4bd7-beb1-71aa937cabf6

-- Generated from ChapterSoftmaxSharpness.lean — solution of BookProof.ChapterSoftmaxSharpness.softmax_smul_query
import Mathlib
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxSharpness



open scoped BigOperators

noncomputable section


open Filter Topology BookProof.ChapterSoftmaxBorn

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta c : ℝ) (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) :
    softmax beta (c • q) k j = softmax (beta * c) q k j := by

  have hinner : ∀ l, (inner ℝ (c • q) (k l) : ℝ) = c * inner ℝ q (k l) := fun l =>
    real_inner_smul_left _ _ _
  have hexp : ∀ l, Real.exp (beta * inner ℝ (c • q) (k l))
      = Real.exp (beta * c * inner ℝ q (k l)) := by
    intro l
    rw [hinner]
    ring_nf
  rw [softmax, softmax, hexp j]
  exact congrArg _ (Finset.sum_congr rfl fun l _ => hexp l)
