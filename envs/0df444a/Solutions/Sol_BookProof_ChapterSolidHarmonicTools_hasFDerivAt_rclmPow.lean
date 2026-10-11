-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonicTools.hasFDerivAt_rclmPow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:03:02.152329+00:00
-- url     : https://prove2.me/submissions/6d6fcb34-f75b-43f9-9545-243838516f35

-- Generated from ChapterSolidHarmonicTools.lean — solution of BookProof.ChapterSolidHarmonicTools.hasFDerivAt_rclmPow
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
theorem solution (L : E →L[ℝ] ℝ) (k : ℕ) (x : E) :
    HasFDerivAt (fun y => (L y) ^ k) (((k : ℝ) * (L x) ^ (k - 1)) • (L : E →L[ℝ] ℝ)) x := (hasDerivAt_pow k (L x)).comp_hasFDerivAt x L.hasFDerivAt
