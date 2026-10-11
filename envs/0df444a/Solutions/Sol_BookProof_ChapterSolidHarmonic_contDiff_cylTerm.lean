-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonic.contDiff_cylTerm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:02:50.9907+00:00
-- url     : https://prove2.me/submissions/3fb8dd52-d403-4c95-8275-d858dd3f0078

-- Generated from ChapterSolidHarmonic.lean — solution of BookProof.ChapterSolidHarmonic.contDiff_cylTerm
import Mathlib
import Definitions.Def_ChapterSolidHarmonic
import Theorems.Thm_BookProof_ChapterSolidHarmonicTools_contDiff_normSqPow
import Theorems.Thm_BookProof_ChapterSolidHarmonicTools_contDiff_rclmPow
import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterSolidHarmonicTools
import Definitions.Def_ChapterLegendrePolynomial
import Definitions.Def_ChapterRadialLaplacian
open BookProof.ChapterSolidHarmonic




open Laplacian InnerProductSpace Polynomial
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open BookProof.ChapterSolidHarmonicTools BookProof.ChapterLegendrePolynomial
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (e : E) (j m : ℕ) :
    ContDiff ℝ 2 fun y : E => (⟪e, y⟫_ℝ) ^ j * (‖y‖ ^ 2) ^ m := (contDiff_rclmPow (innerCLM E e) j).mul (contDiff_normSqPow m)
