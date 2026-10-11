-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonicTools.laplacian_normSqPow
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:57:44.710191+00:00
-- url     : https://prove2.me/submissions/1461154b-a5a5-47a6-b0a2-606bf1ca836f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSolidHarmonicTools.lean — solution of BookProof.ChapterSolidHarmonicTools.laplacian_normSqPow
import Mathlib
import Definitions.Def_ChapterSolidHarmonicTools
import Theorems.Thm_BookProof_ChapterRadialLaplacian_laplacian_comp_normSq
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
open BookProof.ChapterSolidHarmonicTools




open Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open BookProof.ChapterLaplacianProduct
open scoped RealInnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (m : ℕ) (x : E) :
    (Δ fun y : E => (‖y‖ ^ 2) ^ m) x
      = (4 * m * ((m : ℝ) - 1) + 2 * (Module.finrank ℝ E) * m) * (‖x‖ ^ 2) ^ (m - 1) := by

  have hG : ContDiffAt ℝ 2 (fun q : ℝ => q ^ m) (‖x‖ ^ 2) := (contDiff_id.pow m).contDiffAt
  have h := laplacian_comp_normSq (G := fun q : ℝ => q ^ m) (x := x) hG
  rw [h]
  have hd : deriv (fun q : ℝ => q ^ m) = fun q : ℝ => (m : ℝ) * q ^ (m - 1) := by
    funext q; simp
  rw [hd]
  have hdd : deriv (fun q : ℝ => (m : ℝ) * q ^ (m - 1))
      = fun q : ℝ => (m : ℝ) * ((m - 1 : ℕ) : ℝ) * q ^ (m - 1 - 1) := by
    funext q
    rw [deriv_const_mul _ (by fun_prop)]
    simp [mul_assoc]
  rw [hdd]
  rcases m with _ | _ | m
  · simp
  · simp
  · simp only [Nat.add_sub_cancel]
    push_cast
    ring
