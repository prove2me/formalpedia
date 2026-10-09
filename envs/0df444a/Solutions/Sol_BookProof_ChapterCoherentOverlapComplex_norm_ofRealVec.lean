-- Prove2me | solution 1 for BookProof.ChapterCoherentOverlapComplex.norm_ofRealVec
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:28:35.416272+00:00
-- url     : https://prove2.me/submissions/0a1ad635-da12-437b-9364-480d1502e55a

-- Generated from ChapterCoherentOverlapComplex.lean — solution of BookProof.ChapterCoherentOverlapComplex.norm_ofRealVec
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterCoherentOverlapComplex



open scoped BigOperators

noncomputable section


variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q : EuclideanSpace ℝ (Fin n)) : ‖ofRealVec q‖ = ‖q‖ := by

  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  change ‖((q i : ℂ))‖ ^ 2 = ‖q i‖ ^ 2
  simp
