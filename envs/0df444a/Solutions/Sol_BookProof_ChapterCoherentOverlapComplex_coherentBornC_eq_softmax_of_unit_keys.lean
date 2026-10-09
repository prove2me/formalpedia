-- Prove2me | solution 1 for BookProof.ChapterCoherentOverlapComplex.coherentBornC_eq_softmax_of_unit_keys
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:30:25.403991+00:00
-- url     : https://prove2.me/submissions/8649a63d-84c2-4623-8e68-23ae16e350f9

-- Generated from ChapterCoherentOverlapComplex.lean — solution of BookProof.ChapterCoherentOverlapComplex.coherentBornC_eq_softmax_of_unit_keys
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
import Theorems.Thm_BookProof_ChapterCoherentOverlapComplex_coherentBornC_eq_softmax
open BookProof.ChapterCoherentOverlapComplex



open scoped BigOperators

noncomputable section


variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q : EuclideanSpace ℂ (Fin n))
    (k : Fin m → EuclideanSpace ℂ (Fin n)) (hk : ∀ l, ‖k l‖ = 1) (j : Fin m) :
    bornWeightC q k j = softmaxC 2 q k j := coherentBornC_eq_softmax q k 1 hk j
