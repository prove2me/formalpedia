-- Prove2me | solution 1 for BookProof.ChapterSoftmaxBorn.coherentBorn_eq_softmax_of_unit_keys
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T17:19:40.123379+00:00
-- url     : https://prove2.me/submissions/10700fed-60ed-4436-9e05-88c427ee9d6d

-- Generated from ChapterSoftmaxBorn.lean — solution of BookProof.ChapterSoftmaxBorn.coherentBorn_eq_softmax_of_unit_keys
import Mathlib
import Definitions.Def_ChapterSoftmaxBorn
import Theorems.Thm_BookProof_ChapterSoftmaxBorn_coherentBorn_eq_softmax
import Definitions.Def_ChapterCoherentOverlap
open BookProof.ChapterSoftmaxBorn



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (hk : ∀ l, ‖k l‖ = 1) (j : Fin m) :
    bornWeight q k j = softmax 2 q k j := coherentBorn_eq_softmax q k 1 hk j
