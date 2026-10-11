-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonicTools.contDiff_rclmPow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:03:04.489983+00:00
-- url     : https://prove2.me/submissions/678e3cb8-4ab5-4229-9210-a0a3b3d70b55

-- Generated from ChapterSolidHarmonicTools.lean — solution of BookProof.ChapterSolidHarmonicTools.contDiff_rclmPow
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
theorem solution (L : E →L[ℝ] ℝ) (k : ℕ) : ContDiff ℝ 2 fun y : E => (L y) ^ k := (L.contDiff (n := 2)).pow k
