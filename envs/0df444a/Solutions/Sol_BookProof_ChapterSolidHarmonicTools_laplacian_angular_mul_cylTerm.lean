-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonicTools.laplacian_angular_mul_cylTerm
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:57:45.581562+00:00
-- url     : https://prove2.me/submissions/09cd1a4f-57c4-4e96-b6fb-82a404aebad5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSolidHarmonicTools.lean — solution of BookProof.ChapterSolidHarmonicTools.laplacian_angular_mul_cylTerm
import Mathlib
import Definitions.Def_ChapterSolidHarmonicTools
import Theorems.Thm_BookProof_ChapterSolidHarmonicTools_contDiff_rclmPow
import Theorems.Thm_BookProof_ChapterSolidHarmonicTools_contDiff_normSqPow
import Theorems.Thm_BookProof_ChapterSolidHarmonicTools_hasFDerivAt_cylTerm
import Theorems.Thm_BookProof_ChapterSolidHarmonicTools_laplacian_cylTerm
import Theorems.Thm_BookProof_ChapterSolidHarmonicTools_laplacian_angular_mul
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
theorem solution {A : E → ℝ} {x : E} {e : E} (he : ‖e‖ = 1) {μ : ℕ}
    (j m : ℕ) (hA : ContDiffAt ℝ 2 A x) (hharm : (Δ A) x = 0)
    (heuler : fderiv ℝ A x x = μ * A x) (haxis : fderiv ℝ A x e = 0) :
    (Δ fun y : E => A y * ((⟪e, y⟫_ℝ) ^ j * (‖y‖ ^ 2) ^ m)) x
      = A x * ((j : ℝ) * ((j : ℝ) - 1) * (⟪e, x⟫_ℝ) ^ (j - 2) * (‖x‖ ^ 2) ^ m
        + (4 * m * ((m : ℝ) - 1) + 2 * (Module.finrank ℝ E) * m + 4 * j * m + 4 * μ * m)
            * (⟪e, x⟫_ℝ) ^ j * (‖x‖ ^ 2) ^ (m - 1)) := by

  have hB : ContDiffAt ℝ 2 (fun y : E => (⟪e, y⟫_ℝ) ^ j * (‖y‖ ^ 2) ^ m) x :=
    ((contDiff_rclmPow (innerCLM E e) j).mul (contDiff_normSqPow m)).contDiffAt
  have hgrad : fderiv ℝ (fun y : E => (⟪e, y⟫_ℝ) ^ j * (‖y‖ ^ 2) ^ m) x
      = ((j : ℝ) * (⟪e, x⟫_ℝ) ^ (j - 1) * (‖x‖ ^ 2) ^ m) • innerCLM E e
        + (2 * m * (⟪e, x⟫_ℝ) ^ j * (‖x‖ ^ 2) ^ (m - 1)) • innerCLM E x :=
    (hasFDerivAt_cylTerm e j m x).fderiv
  rw [laplacian_angular_mul hA hB hharm heuler haxis hgrad, laplacian_cylTerm e he j m x]
  ring
