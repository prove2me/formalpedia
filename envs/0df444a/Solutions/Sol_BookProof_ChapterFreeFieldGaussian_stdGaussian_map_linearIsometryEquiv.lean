-- Prove2me | solution 1 for BookProof.ChapterFreeFieldGaussian.stdGaussian_map_linearIsometryEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T00:24:56.720634+00:00
-- url     : https://prove2.me/submissions/cc08761f-d770-493a-b161-55130f78ecd1

import Mathlib
import Definitions.Def_ChapterFreeFieldGaussian

set_option autoImplicit false

open BookProof.ChapterFreeFieldGaussian MeasureTheory in
theorem solution {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (stdGaussian n).map L = stdGaussian n := by
  have h : stdGaussian n = ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n)) :=
    ProbabilityTheory.map_pi_eq_stdGaussian
  rw [h]
  exact ProbabilityTheory.stdGaussian_map L
