-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonic.fderiv_angular
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:45:46.755896+00:00
-- url     : https://prove2.me/submissions/414935c6-42e5-41ad-93c3-e5cfe0290ab8

-- Generated from ChapterSolidHarmonic.lean — solution of BookProof.ChapterSolidHarmonic.fderiv_angular
import Mathlib
import Definitions.Def_ChapterSolidHarmonic
import Theorems.Thm_BookProof_ChapterSolidHarmonicTools_hasFDerivAt_clmPow
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
theorem solution (u v : E) (μ : ℕ) (x w : E) :
    fderiv ℝ (angular u v μ) x w = ((μ : ℂ) * (nullCLM u v x) ^ (μ - 1) * nullCLM u v w).re := by

  have h : HasFDerivAt (angular u v μ)
      (Complex.reCLM.comp (((μ : ℂ) * (nullCLM u v x) ^ (μ - 1)) • (nullCLM u v))) x :=
    Complex.reCLM.hasFDerivAt.comp x (hasFDerivAt_clmPow (nullCLM u v) μ x)
  rw [h.fderiv]
  simp [mul_assoc]
