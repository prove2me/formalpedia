-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonic.contDiff_radialFactor
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:02:56.060878+00:00
-- url     : https://prove2.me/submissions/81d7329b-a79f-4109-a584-586765591708

-- Generated from ChapterSolidHarmonic.lean — solution of BookProof.ChapterSolidHarmonic.contDiff_radialFactor
import Mathlib
import Definitions.Def_ChapterSolidHarmonic
import Theorems.Thm_BookProof_ChapterSolidHarmonic_contDiff_cylTerm
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
theorem solution (e : E) (l μ : ℕ) : ContDiff ℝ 2 (radialFactor e l μ) := by

  refine ContDiff.sum fun m _ => ?_
  exact contDiff_const.mul (contDiff_cylTerm e (l - μ - 2 * m) m)
