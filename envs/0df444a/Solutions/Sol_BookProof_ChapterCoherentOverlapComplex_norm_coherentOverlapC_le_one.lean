-- Prove2me | solution 1 for BookProof.ChapterCoherentOverlapComplex.norm_coherentOverlapC_le_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:28:20.476985+00:00
-- url     : https://prove2.me/submissions/849a8075-7d68-44e8-8e70-c3d403152e06

-- Generated from ChapterCoherentOverlapComplex.lean — solution of BookProof.ChapterCoherentOverlapComplex.norm_coherentOverlapC_le_one
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
import Theorems.Thm_BookProof_ChapterCoherentOverlapComplex_norm_coherentOverlapC
open BookProof.ChapterCoherentOverlapComplex



open scoped BigOperators

noncomputable section


variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q k : EuclideanSpace ℂ (Fin n)) :
    ‖coherentOverlapC q k‖ ≤ 1 := by

  rw [norm_coherentOverlapC, Real.exp_le_one_iff]
  have h1 : (inner ℂ q k : ℂ).re ≤ ‖(inner ℂ q k : ℂ)‖ := Complex.re_le_norm _
  have h2 : ‖(inner ℂ q k : ℂ)‖ ≤ ‖q‖ * ‖k‖ := norm_inner_le_norm _ _
  have h3 : 2 * (‖q‖ * ‖k‖) ≤ ‖q‖ ^ 2 + ‖k‖ ^ 2 := by nlinarith [sq_nonneg (‖q‖ - ‖k‖)]
  linarith
