-- Prove2me | solution 1 for BookProof.ChapterLegendrePolynomial.natDegree_Xsq_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:30:49.446518+00:00
-- url     : https://prove2.me/submissions/dab6bb58-8711-4f00-b8c5-457dc37301b9

-- Generated from ChapterLegendrePolynomial.lean — solution of BookProof.ChapterLegendrePolynomial.natDegree_Xsq_sub_one
import Mathlib
import Definitions.Def_ChapterLegendrePolynomial
open BookProof.ChapterLegendrePolynomial




open Polynomial

set_option maxHeartbeats 1000000 in
theorem solution : (X ^ 2 - 1 : ℝ[X]).natDegree = 2 := by

  have h : (X ^ 2 - 1 : ℝ[X]) = X ^ 2 - C 1 := by simp
  rw [h, natDegree_X_pow_sub_C]
