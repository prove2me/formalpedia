-- Prove2me | solution 1 for BookProof.ChapterCoherentOverlapComplex.bornDenomC_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:29:06.024753+00:00
-- url     : https://prove2.me/submissions/9a77e9c0-d6d0-40fb-9fe5-e4c7444c9f57

-- Generated from ChapterCoherentOverlapComplex.lean — solution of BookProof.ChapterCoherentOverlapComplex.bornDenomC_pos
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
import Theorems.Thm_BookProof_ChapterCoherentOverlapComplex_bornNumerC_pos
open BookProof.ChapterCoherentOverlapComplex



open scoped BigOperators

noncomputable section


variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ (Fin n))
    (j : Fin m) : 0 < ∑ l, bornNumerC q (k l) := Finset.sum_pos (fun l _ => bornNumerC_pos q (k l)) ⟨j, Finset.mem_univ j⟩
