-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonicTools.contDiff_clmPow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:03:03.255291+00:00
-- url     : https://prove2.me/submissions/a6c35c93-18b5-4234-8277-4df9e63cfbd0

-- Generated from ChapterSolidHarmonicTools.lean — solution of BookProof.ChapterSolidHarmonicTools.contDiff_clmPow
import Mathlib
import Definitions.Def_ChapterSolidHarmonicTools
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
open BookProof.ChapterSolidHarmonicTools




open Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open BookProof.ChapterLaplacianProduct
open scoped RealInnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (ψ : E →L[ℝ] ℂ) (k : ℕ) : ContDiff ℝ 2 fun y : E => (ψ y) ^ k := (ψ.contDiff (n := 2)).pow k
