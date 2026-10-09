-- Prove2me | solution 1 for BookProof.ChapterCoherentOverlapComplex.inner_ofRealVec
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:28:48.919985+00:00
-- url     : https://prove2.me/submissions/34ee6b74-bd0c-4245-8d7b-53d27b3d3390

-- Generated from ChapterCoherentOverlapComplex.lean — solution of BookProof.ChapterCoherentOverlapComplex.inner_ofRealVec
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterCoherentOverlapComplex



open scoped BigOperators

noncomputable section


variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q k : EuclideanSpace ℝ (Fin n)) :
    inner ℂ (ofRealVec q) (ofRealVec k) = ((inner ℝ q k : ℝ) : ℂ) := by

  rw [PiLp.inner_apply, PiLp.inner_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [RCLike.inner_apply, ofRealVec, mul_comm]
