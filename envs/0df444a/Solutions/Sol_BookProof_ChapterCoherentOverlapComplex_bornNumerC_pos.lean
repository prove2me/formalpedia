-- Prove2me | solution 1 for BookProof.ChapterCoherentOverlapComplex.bornNumerC_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:28:51.914848+00:00
-- url     : https://prove2.me/submissions/6993668a-69ef-49ec-9e8b-814b225ed9a1

-- Generated from ChapterCoherentOverlapComplex.lean — solution of BookProof.ChapterCoherentOverlapComplex.bornNumerC_pos
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
import Theorems.Thm_BookProof_ChapterCoherentOverlapComplex_coherentOverlapC_ne_zero
open BookProof.ChapterCoherentOverlapComplex



open scoped BigOperators

noncomputable section


variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q k : EuclideanSpace ℂ (Fin n)) : 0 < bornNumerC q k := by

  rw [bornNumerC]
  exact pow_pos (norm_pos_iff.2 (coherentOverlapC_ne_zero q k)) 2
