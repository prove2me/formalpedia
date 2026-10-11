-- Prove2me | solution 1 for BookProof.ChapterSoftmaxSharpness.ampBorn_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:43:38.104981+00:00
-- url     : https://prove2.me/submissions/42507784-73a7-4f96-af20-f79b15212140

-- Generated from ChapterSoftmaxSharpness.lean — solution of BookProof.ChapterSoftmaxSharpness.ampBorn_nonneg
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
theorem solution (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n))
    (j : Fin m) : 0 ≤ ampBorn q k j := by

  refine div_nonneg (sq_nonneg _) (Finset.sum_nonneg fun l _ => sq_nonneg _)
