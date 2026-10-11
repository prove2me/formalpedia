-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonic.contDiff_angular
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:45:29.305654+00:00
-- url     : https://prove2.me/submissions/5e82723b-948e-4117-baf0-7cafe82025b5

-- Generated from ChapterSolidHarmonic.lean — solution of BookProof.ChapterSolidHarmonic.contDiff_angular
import Mathlib
import Definitions.Def_ChapterSolidHarmonic
import Theorems.Thm_BookProof_ChapterSolidHarmonicTools_contDiff_clmPow
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
theorem solution (u v : E) (μ : ℕ) : ContDiff ℝ 2 (angular u v μ) := Complex.reCLM.contDiff.comp (contDiff_clmPow (nullCLM u v) μ)
