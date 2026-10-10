-- Prove2me | solution 1 for BookProof.ChapterLaplacianProduct.sum_inner_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:21:25.456566+00:00
-- url     : https://prove2.me/submissions/4a70215c-4c51-44ee-acb7-a199bec2f286

-- Generated from ChapterLaplacianProduct.lean — solution of BookProof.ChapterLaplacianProduct.sum_inner_mul_apply
import Mathlib
import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterRadialLaplacian
open BookProof.ChapterLaplacianProduct




open Filter Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution [FiniteDimensional ℝ E] (L : E →L[ℝ] ℝ) (x : E) :
    ∑ i, ⟪x, (stdOrthonormalBasis ℝ E) i⟫ * L ((stdOrthonormalBasis ℝ E) i) = L x := by

  have hx : ∑ i, ⟪(stdOrthonormalBasis ℝ E) i, x⟫ • (stdOrthonormalBasis ℝ E) i = x :=
    (stdOrthonormalBasis ℝ E).sum_repr' x
  calc ∑ i, ⟪x, (stdOrthonormalBasis ℝ E) i⟫ * L ((stdOrthonormalBasis ℝ E) i)
      = L (∑ i, ⟪(stdOrthonormalBasis ℝ E) i, x⟫ • (stdOrthonormalBasis ℝ E) i) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, real_inner_comm]
        simp
    _ = L x := by rw [hx]
