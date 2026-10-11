-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonic.contDiff_solidHarmonic
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:57:41.796526+00:00
-- url     : https://prove2.me/submissions/ca7da40f-c01b-466e-8f1b-6b2152fbcda5

-- Generated from ChapterSolidHarmonic.lean — solution of BookProof.ChapterSolidHarmonic.contDiff_solidHarmonic
import Mathlib
import Definitions.Def_ChapterSolidHarmonic
import Theorems.Thm_BookProof_ChapterSolidHarmonic_contDiff_angular
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
theorem solution (u v e : E) (l μ : ℕ) : ContDiff ℝ 2 (solidHarmonic u v e l μ) := (contDiff_angular u v μ).mul (contDiff_radialFactor e l μ)
