-- Prove2me | solution 1 for BookProof.ChapterSoftmaxSharpness.softmax_eq_scoreSoftmax
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:43:40.081228+00:00
-- url     : https://prove2.me/submissions/fa3e90ff-4116-420e-9eb8-c06cb33fa0c1

-- Generated from ChapterSoftmaxSharpness.lean — solution of BookProof.ChapterSoftmaxSharpness.softmax_eq_scoreSoftmax
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
theorem solution (beta : ℝ) (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) :
    softmax beta q k j = scoreSoftmax beta (fun l => inner ℝ q (k l)) j := rfl
