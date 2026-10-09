-- Prove2me | solution 1 for BookProof.ChapterCoherentOverlapComplex.bornNumerC_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:29:04.971793+00:00
-- url     : https://prove2.me/submissions/105f40b5-9b28-4f86-8e4c-c09c25c1eaa8

-- Generated from ChapterCoherentOverlapComplex.lean — solution of BookProof.ChapterCoherentOverlapComplex.bornNumerC_ofReal
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
import Theorems.Thm_BookProof_ChapterCoherentOverlapComplex_coherentOverlapC_ofReal
import Theorems.Thm_BookProof_ChapterCoherentOverlap_coherentOverlap_pos
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterCoherentOverlapComplex



open scoped BigOperators

noncomputable section


variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q k : EuclideanSpace ℝ (Fin n)) :
    bornNumerC (ofRealVec q) (ofRealVec k)
      = BookProof.ChapterSoftmaxBorn.bornNumer q k := by

  rw [bornNumerC, coherentOverlapC_ofReal, BookProof.ChapterSoftmaxBorn.bornNumer,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (BookProof.ChapterCoherentOverlap.coherentOverlap_pos q k)]
