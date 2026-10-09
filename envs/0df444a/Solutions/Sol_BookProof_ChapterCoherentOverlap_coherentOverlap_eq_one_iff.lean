-- Prove2me | solution 1 for BookProof.ChapterCoherentOverlap.coherentOverlap_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:27:12.34119+00:00
-- url     : https://prove2.me/submissions/89070502-692b-4028-9339-9e6a7a4c7665

-- Generated from ChapterCoherentOverlap.lean — solution of BookProof.ChapterCoherentOverlap.coherentOverlap_eq_one_iff
import Mathlib
import Definitions.Def_ChapterCoherentOverlap
import Theorems.Thm_BookProof_ChapterCoherentOverlap_coherentOverlap_eq_gaussian
open BookProof.ChapterCoherentOverlap



open scoped BigOperators

noncomputable section


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q k : EuclideanSpace ℝ (Fin n)) :
    coherentOverlap q k = 1 ↔ q = k := by

  rw [coherentOverlap_eq_gaussian, Real.exp_eq_one_iff]
  constructor
  · intro h
    have hnorm : ‖q - k‖ ^ 2 = 0 := by linarith
    have : ‖q - k‖ = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hnorm
      exact this
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  · rintro rfl
    simp
