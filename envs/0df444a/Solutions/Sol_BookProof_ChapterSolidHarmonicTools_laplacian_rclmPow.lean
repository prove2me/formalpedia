-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonicTools.laplacian_rclmPow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:03:10.626096+00:00
-- url     : https://prove2.me/submissions/093b74ec-9b65-4733-980b-d89f0ca23dd2

-- Generated from ChapterSolidHarmonicTools.lean — solution of BookProof.ChapterSolidHarmonicTools.laplacian_rclmPow
import Mathlib
import Definitions.Def_ChapterSolidHarmonicTools
import Theorems.Thm_BookProof_ChapterSolidHarmonicTools_fderiv_fderiv_rclmPow
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
theorem solution (L : E →L[ℝ] ℝ) (k : ℕ) (x : E) :
    (Δ fun y => (L y) ^ k) x
      = (k : ℝ) * ((k : ℝ) - 1) * (L x) ^ (k - 2)
          * ∑ i, (L (stdOrthonormalBasis ℝ E i)) ^ 2 := by

  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    fderiv_fderiv_rclmPow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
