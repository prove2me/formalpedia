-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonic.fderiv_angularIm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:45:47.654229+00:00
-- url     : https://prove2.me/submissions/81842788-9a57-4721-8e6c-396a1bc02c4d

-- Generated from ChapterSolidHarmonic.lean — solution of BookProof.ChapterSolidHarmonic.fderiv_angularIm
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
    fderiv ℝ (angularIm u v μ) x w = ((μ : ℂ) * (nullCLM u v x) ^ (μ - 1) * nullCLM u v w).im := by

  have h : HasFDerivAt (angularIm u v μ)
      (Complex.imCLM.comp (((μ : ℂ) * (nullCLM u v x) ^ (μ - 1)) • (nullCLM u v))) x :=
    Complex.imCLM.hasFDerivAt.comp x (hasFDerivAt_clmPow (nullCLM u v) μ x)
  rw [h.fderiv]
  simp [mul_assoc]
