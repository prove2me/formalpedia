-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonicTools.laplacian_angular_mul
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:21:39.536696+00:00
-- url     : https://prove2.me/submissions/4a51945f-d552-4f34-9cba-d57182eae868

import Definitions.Def_ChapterLaplacianProduct
import Mathlib
import Definitions.Def_ChapterSolidHarmonicTools
import Definitions.Def_ChapterRadialLaplacian
import Theorems.Thm_BookProof_ChapterLaplacianProduct_laplacian_mul
import Theorems.Thm_BookProof_ChapterLaplacianProduct_sum_inner_mul_apply
-- Generated from ChapterSolidHarmonicTools.lean — theorem BookProof.ChapterSolidHarmonicTools.laplacian_angular_mul
open BookProof.ChapterRadialLaplacian
open BookProof.ChapterSolidHarmonicTools



open Laplacian InnerProductSpace BookProof.ChapterRadialLaplacian
open BookProof.ChapterLaplacianProduct
open scoped RealInnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]


theorem solution {A B : E → ℝ} {x : E} {α β : ℝ} {e : E} {μ : ℕ}
    (hA : ContDiffAt ℝ 2 A x) (hB : ContDiffAt ℝ 2 B x)
    (hharm : (Δ A) x = 0) (heuler : fderiv ℝ A x x = μ * A x) (haxis : fderiv ℝ A x e = 0)
    (hgrad : fderiv ℝ B x = α • innerCLM E e + β • innerCLM E x) :
    (Δ fun y : E => A y * B y) x = A x * (Δ B) x + 2 * β * (μ : ℝ) * A x := by
  rw [BookProof.ChapterLaplacianProduct.laplacian_mul hA hB, hharm, hgrad]
  have hs : ∑ i, fderiv ℝ A x ((stdOrthonormalBasis ℝ E) i)
      * (α • innerCLM E e + β • innerCLM E x) ((stdOrthonormalBasis ℝ E) i)
      = α * fderiv ℝ A x e + β * fderiv ℝ A x x := by
    have h1 := BookProof.ChapterLaplacianProduct.sum_inner_mul_apply (fderiv ℝ A x) e
    have h2 := BookProof.ChapterLaplacianProduct.sum_inner_mul_apply (fderiv ℝ A x) x
    rw [← h1, ← h2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [show innerCLM E e ((stdOrthonormalBasis ℝ E) i) = ⟪e, (stdOrthonormalBasis ℝ E) i⟫_ℝ from rfl,
      show innerCLM E x ((stdOrthonormalBasis ℝ E) i) = ⟪x, (stdOrthonormalBasis ℝ E) i⟫_ℝ from rfl]
    ring
  rw [hs, haxis, heuler]
  ring

