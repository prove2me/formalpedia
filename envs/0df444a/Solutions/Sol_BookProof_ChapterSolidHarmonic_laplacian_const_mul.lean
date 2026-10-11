-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonic.laplacian_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:02:49.525718+00:00
-- url     : https://prove2.me/submissions/e6ef2ca0-297c-47f3-a610-6b65ddf4dc5b

-- Generated from ChapterSolidHarmonic.lean — solution of BookProof.ChapterSolidHarmonic.laplacian_const_mul
import Mathlib
import Definitions.Def_ChapterSolidHarmonic
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
theorem solution {f : E → ℝ} {x : E} (c : ℝ) (hf : ContDiffAt ℝ 2 f x) :
    (Δ fun y => c * f y) x = c * (Δ f) x := by

  have hrw : (fun y => c * f y) = c • f := by funext y; simp
  rw [hrw, laplacian_smul c hf]
  simp
