-- Prove2me | solution 1 for BookProof.ChapterH1.eigenvalue_mem_numericalRange
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:17:25.897243+00:00
-- url     : https://prove2.me/submissions/e217de70-8ad2-418a-88b6-d50d7ab543f1

-- Generated from ChapterH1.lean — solution of BookProof.ChapterH1.eigenvalue_mem_numericalRange
import Mathlib
import Definitions.Def_ChapterH1
open BookProof.ChapterH1







open scoped BigOperators
open intervalIntegral


noncomputable section














variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution (A : E →ₗ[ℂ] E) (l : ℂ) (v : E)
    (hv : ‖v‖ = 1) (hAv : A v = l • v) : l ∈ numericalRange A := by

  use v;
  simp_all [ inner_self_eq_norm_sq_to_K ]
