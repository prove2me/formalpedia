-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonic.contDiff_solidHarmonicIm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:57:42.692748+00:00
-- url     : https://prove2.me/submissions/061a7ffc-c1a5-470c-9054-e27b8c64241b

-- Generated from ChapterSolidHarmonic.lean — solution of BookProof.ChapterSolidHarmonic.contDiff_solidHarmonicIm
import Mathlib
import Definitions.Def_ChapterSolidHarmonic
import Theorems.Thm_BookProof_ChapterSolidHarmonic_contDiff_angularIm
import Theorems.Thm_BookProof_ChapterSolidHarmonic_contDiff_radialFactor
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
theorem solution (u v e : E) (l μ : ℕ) :
    ContDiff ℝ 2 (solidHarmonicIm u v e l μ) := (contDiff_angularIm u v μ).mul (contDiff_radialFactor e l μ)
