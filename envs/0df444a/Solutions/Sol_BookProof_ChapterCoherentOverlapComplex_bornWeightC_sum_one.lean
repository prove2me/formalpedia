-- Prove2me | solution 1 for BookProof.ChapterCoherentOverlapComplex.bornWeightC_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:29:45.493748+00:00
-- url     : https://prove2.me/submissions/546b04c4-d6a4-4ac6-8491-97f11b9d7a19

-- Generated from ChapterCoherentOverlapComplex.lean — solution of BookProof.ChapterCoherentOverlapComplex.bornWeightC_sum_one
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
import Theorems.Thm_BookProof_ChapterCoherentOverlapComplex_bornDenomC_pos
open BookProof.ChapterCoherentOverlapComplex



open scoped BigOperators

noncomputable section


variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q : EuclideanSpace ℂ (Fin n))
    (k : Fin m → EuclideanSpace ℂ (Fin n)) (j₀ : Fin m) :
    ∑ j, bornWeightC q k j = 1 := by

  simp only [bornWeightC]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (bornDenomC_pos q k j₀))
