-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonicTools.fderiv_normSqPow
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:57:43.653293+00:00
-- url     : https://prove2.me/submissions/1392650d-fd49-48c4-ae12-1d4d623b829a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSolidHarmonicTools.lean — solution of BookProof.ChapterSolidHarmonicTools.fderiv_normSqPow
import Mathlib
import Definitions.Def_ChapterSolidHarmonicTools
import Theorems.Thm_BookProof_ChapterRadialLaplacian_fderiv_comp_normSq
import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterRadialLaplacian
open BookProof.ChapterSolidHarmonicTools




open Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open BookProof.ChapterLaplacianProduct
open scoped RealInnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (m : ℕ) (x : E) :
    fderiv ℝ (fun y : E => (‖y‖ ^ 2) ^ m) x = (2 * m * (‖x‖ ^ 2) ^ (m - 1)) • innerCLM E x := by

  have hG : ContDiffAt ℝ 2 (fun q : ℝ => q ^ m) (‖x‖ ^ 2) := (contDiff_id.pow m).contDiffAt
  have h := (fderiv_comp_normSq (G := fun q : ℝ => q ^ m) hG).self_of_nhds
  have hd : deriv (fun q : ℝ => q ^ m) = fun q : ℝ => (m : ℝ) * q ^ (m - 1) := by
    funext q; simp
  rw [h, hd]
  simp only [mul_assoc]
