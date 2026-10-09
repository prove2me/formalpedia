-- Prove2me | solution 1 for BookProof.ChapterCoherentOverlapComplex.coherentOverlapC_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:28:49.912851+00:00
-- url     : https://prove2.me/submissions/0a404a4e-2e98-4f6e-adc3-566866d74afe

-- Generated from ChapterCoherentOverlapComplex.lean — solution of BookProof.ChapterCoherentOverlapComplex.coherentOverlapC_ofReal
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
import Theorems.Thm_BookProof_ChapterCoherentOverlapComplex_norm_ofRealVec
import Theorems.Thm_BookProof_ChapterCoherentOverlapComplex_inner_ofRealVec
open BookProof.ChapterCoherentOverlapComplex



open scoped BigOperators

noncomputable section


variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q k : EuclideanSpace ℝ (Fin n)) :
    coherentOverlapC (ofRealVec q) (ofRealVec k)
      = ((BookProof.ChapterCoherentOverlap.coherentOverlap q k : ℝ) : ℂ) := by

  rw [coherentOverlapC, inner_ofRealVec, norm_ofRealVec, norm_ofRealVec,
    BookProof.ChapterCoherentOverlap.coherentOverlap, Complex.ofReal_exp]
  congr 1
  push_cast
  ring
