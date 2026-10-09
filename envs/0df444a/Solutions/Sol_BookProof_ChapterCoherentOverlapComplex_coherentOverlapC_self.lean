-- Prove2me | solution 1 for BookProof.ChapterCoherentOverlapComplex.coherentOverlapC_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:28:19.406387+00:00
-- url     : https://prove2.me/submissions/57d4cc9c-2165-466a-9571-fed8f8056951

-- Generated from ChapterCoherentOverlapComplex.lean — solution of BookProof.ChapterCoherentOverlapComplex.coherentOverlapC_self
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterCoherentOverlapComplex



open scoped BigOperators

noncomputable section


variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q : EuclideanSpace ℂ (Fin n)) :
    coherentOverlapC q q = 1 := by

  rw [coherentOverlapC, inner_self_eq_norm_sq_to_K]
  norm_num
  rw [show -(‖q‖ : ℂ) ^ 2 / 2 - (‖q‖ : ℂ) ^ 2 / 2 + (‖q‖ : ℂ) ^ 2 = 0 from by ring]
  exact Complex.exp_zero
