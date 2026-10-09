-- Prove2me | solution 1 for BookProof.ChapterCoherentOverlapComplex.coherentOverlapC_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:28:06.001958+00:00
-- url     : https://prove2.me/submissions/654ac3fe-600a-407b-b591-93776f426610

-- Generated from ChapterCoherentOverlapComplex.lean — solution of BookProof.ChapterCoherentOverlapComplex.coherentOverlapC_ne_zero
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterCoherentOverlapComplex



open scoped BigOperators

noncomputable section


variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q k : EuclideanSpace ℂ (Fin n)) :
    coherentOverlapC q k ≠ 0 := Complex.exp_ne_zero _
