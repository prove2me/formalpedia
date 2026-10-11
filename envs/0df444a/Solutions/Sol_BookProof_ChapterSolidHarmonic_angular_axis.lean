-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonic.angular_axis
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:46:43.356911+00:00
-- url     : https://prove2.me/submissions/b034817a-c7fe-41eb-955f-cc5ec9dacd2b

-- Generated from ChapterSolidHarmonic.lean — solution of BookProof.ChapterSolidHarmonic.angular_axis
import Mathlib
import Definitions.Def_ChapterSolidHarmonic
import Theorems.Thm_BookProof_ChapterSolidHarmonic_fderiv_angular
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterSolidHarmonicTools
import Definitions.Def_ChapterLegendrePolynomial
open BookProof.ChapterSolidHarmonic




open Laplacian InnerProductSpace Polynomial
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open BookProof.ChapterSolidHarmonicTools BookProof.ChapterLegendrePolynomial
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {u v e : E} (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0) (μ : ℕ) (x : E) :
    fderiv ℝ (angular u v μ) x e = 0 := by

  have h0 : nullCLM u v e = 0 := by
    rw [nullCLM_apply, hue, hve]
    simp
  rw [fderiv_angular, h0, mul_zero]
  simp
