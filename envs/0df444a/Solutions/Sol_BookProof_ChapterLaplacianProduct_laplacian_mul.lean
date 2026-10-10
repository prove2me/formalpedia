-- Prove2me | solution 1 for BookProof.ChapterLaplacianProduct.laplacian_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:20:22.358127+00:00
-- url     : https://prove2.me/submissions/cfc58bf7-8ca0-41a3-a915-3c42b9e87c50

-- Generated from ChapterLaplacianProduct.lean — solution of BookProof.ChapterLaplacianProduct.laplacian_mul
import Mathlib
import Definitions.Def_ChapterLaplacianProduct
import Theorems.Thm_BookProof_ChapterLaplacianProduct_fderiv_fderiv_mul
import Definitions.Def_ChapterRadialLaplacian
open BookProof.ChapterLaplacianProduct




open Filter Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution [FiniteDimensional ℝ E] {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    (Δ fun y : E => f y * g y) x
      = (Δ f) x * g x + f x * (Δ g) x
        + 2 * ∑ i, fderiv ℝ f x ((stdOrthonormalBasis ℝ E) i)
            * fderiv ℝ g x ((stdOrthonormalBasis ℝ E) i) := by

  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    laplacian_eq_iteratedFDeriv_stdOrthonormalBasis f,
    laplacian_eq_iteratedFDeriv_stdOrthonormalBasis g]
  have hterm : ∀ i, iteratedFDeriv ℝ 2 (fun y : E => f y * g y) x
      ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i]
      = g x * iteratedFDeriv ℝ 2 f x
          ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i]
        + f x * iteratedFDeriv ℝ 2 g x
          ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i]
        + 2 * (fderiv ℝ f x ((stdOrthonormalBasis ℝ E) i)
            * fderiv ℝ g x ((stdOrthonormalBasis ℝ E) i)) := by
    intro i
    rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, iteratedFDeriv_two_apply,
      fderiv_fderiv_mul hf hg]
    simp
    ring
  simp only [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]
  ring
