-- Prove2me | solution 1 for BookProof.ChapterCoherentFidelity.bornWeightC_eq_fidelity_normalized
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:10:03.895602+00:00
-- url     : https://prove2.me/submissions/e577d869-3b8c-40e7-831a-1334088ef77a

-- Generated from ChapterCoherentFidelity.lean — solution of BookProof.ChapterCoherentFidelity.bornWeightC_eq_fidelity_normalized
import Mathlib
import Definitions.Def_ChapterCoherentFidelity
open BookProof.ChapterCoherentFidelity



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex BookProof.ChapterSoftmaxSharpness

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q : EuclideanSpace ℂ (Fin n))
    (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) :
    bornWeightC q k j = fidelityC q (k j) / ∑ l, fidelityC q (k l) := rfl
