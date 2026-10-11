-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonicTools.laplacian_clmPow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:03:09.223514+00:00
-- url     : https://prove2.me/submissions/a3149fd5-f2f2-4e48-adeb-81bf24295491

-- Generated from ChapterSolidHarmonicTools.lean — solution of BookProof.ChapterSolidHarmonicTools.laplacian_clmPow
import Mathlib
import Definitions.Def_ChapterSolidHarmonicTools
import Theorems.Thm_BookProof_ChapterSolidHarmonicTools_fderiv_fderiv_clmPow
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
theorem solution (ψ : E →L[ℝ] ℂ) (k : ℕ) (x : E) :
    (Δ fun y => (ψ y) ^ k) x
      = (k : ℂ) * ((k : ℂ) - 1) * (ψ x) ^ (k - 2)
          * ∑ i, (ψ (stdOrthonormalBasis ℝ E i)) ^ 2 := by

  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    fderiv_fderiv_clmPow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
