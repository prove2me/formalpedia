-- Prove2me | solution 1 for BookProof.ChapterCoherentFidelity.fidelityC_eq_bornNumerC
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:08:23.244381+00:00
-- url     : https://prove2.me/submissions/b7110cf8-deec-4efe-ac2e-481bb057edc3

-- Generated from ChapterCoherentFidelity.lean — solution of BookProof.ChapterCoherentFidelity.fidelityC_eq_bornNumerC
import Mathlib
import Definitions.Def_ChapterCoherentFidelity
open BookProof.ChapterCoherentFidelity



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex BookProof.ChapterSoftmaxSharpness

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q k : EuclideanSpace ℂ (Fin n)) :
    fidelityC q k = bornNumerC q k := rfl
