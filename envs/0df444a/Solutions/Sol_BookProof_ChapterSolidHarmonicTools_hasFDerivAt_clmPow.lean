-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonicTools.hasFDerivAt_clmPow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:03:01.00133+00:00
-- url     : https://prove2.me/submissions/ae079f63-1d44-43fa-9ae7-ac75126d9a27

-- Generated from ChapterSolidHarmonicTools.lean — solution of BookProof.ChapterSolidHarmonicTools.hasFDerivAt_clmPow
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
theorem solution (ψ : E →L[ℝ] ℂ) (k : ℕ) (x : E) :
    HasFDerivAt (fun y => (ψ y) ^ k) (((k : ℂ) * (ψ x) ^ (k - 1)) • (ψ : E →L[ℝ] ℂ)) x := (hasDerivAt_pow k (ψ x)).comp_hasFDerivAt x ψ.hasFDerivAt
