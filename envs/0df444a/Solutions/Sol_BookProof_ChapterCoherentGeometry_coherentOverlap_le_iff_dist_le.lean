-- Prove2me | solution 1 for BookProof.ChapterCoherentGeometry.coherentOverlap_le_iff_dist_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:10:56.18729+00:00
-- url     : https://prove2.me/submissions/118813cb-9afa-4f5c-aa89-347d6a6767ea

-- Generated from ChapterCoherentGeometry.lean — solution of BookProof.ChapterCoherentGeometry.coherentOverlap_le_iff_dist_le
import Mathlib
import Definitions.Def_ChapterCoherentGeometry
import Theorems.Thm_BookProof_ChapterCoherentOverlap_coherentOverlap_eq_gaussian
open BookProof.ChapterCoherentGeometry



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap BookProof.ChapterSoftmaxBorn

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q k k' : EuclideanSpace ℝ (Fin n)) :
    coherentOverlap q k ≤ coherentOverlap q k' ↔ ‖q - k'‖ ≤ ‖q - k‖ := by

  rw [coherentOverlap_eq_gaussian, coherentOverlap_eq_gaussian, Real.exp_le_exp]
  constructor
  · intro h
    nlinarith [norm_nonneg (q - k), norm_nonneg (q - k')]
  · intro h
    nlinarith [norm_nonneg (q - k), norm_nonneg (q - k')]
