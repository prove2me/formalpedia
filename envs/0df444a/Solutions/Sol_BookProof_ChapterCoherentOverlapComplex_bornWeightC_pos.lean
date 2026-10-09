-- Prove2me | solution 1 for BookProof.ChapterCoherentOverlapComplex.bornWeightC_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:29:44.523639+00:00
-- url     : https://prove2.me/submissions/a6a2b347-b230-4170-a586-dc6c553357b6

-- Generated from ChapterCoherentOverlapComplex.lean — solution of BookProof.ChapterCoherentOverlapComplex.bornWeightC_pos
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
import Theorems.Thm_BookProof_ChapterCoherentOverlapComplex_bornNumerC_pos
import Theorems.Thm_BookProof_ChapterCoherentOverlapComplex_bornDenomC_pos
open BookProof.ChapterCoherentOverlapComplex



open scoped BigOperators

noncomputable section


variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ (Fin n))
    (j : Fin m) : 0 < bornWeightC q k j := div_pos (bornNumerC_pos q (k j)) (bornDenomC_pos q k j)
