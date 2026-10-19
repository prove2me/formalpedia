-- Prove2me | solution 1 for BookProof.ChapterSolidHarmonic.solidHarmonic_euler
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:47:29.106696+00:00
-- url     : https://prove2.me/submissions/d66b72f7-4568-47b2-88ea-700c00d8e7fb

-- Generated from ChapterSolidHarmonic.lean — solution of BookProof.ChapterSolidHarmonic.solidHarmonic_euler
import Mathlib
import Definitions.Def_ChapterSolidHarmonic
import Theorems.Thm_BookProof_ChapterSolidHarmonic_contDiff_angular
import Theorems.Thm_BookProof_ChapterSolidHarmonic_angular_euler
import Theorems.Thm_BookProof_ChapterSolidHarmonic_contDiff_radialFactor
import Theorems.Thm_BookProof_ChapterSolidHarmonic_radialFactor_euler
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
theorem solution (u v e : E) {l μ : ℕ} (hμ : μ ≤ l) (x : E) :
    fderiv ℝ (solidHarmonic u v e l μ) x x = (l : ℝ) * solidHarmonic u v e l μ x := by

  have hA : HasFDerivAt (angular u v μ) (fderiv ℝ (angular u v μ) x) x :=
    ((contDiff_angular u v μ).differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hB : HasFDerivAt (radialFactor e l μ) (fderiv ℝ (radialFactor e l μ) x) x :=
    ((contDiff_radialFactor e l μ).differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hprod := (hA.mul hB).fderiv
  have hrw : solidHarmonic u v e l μ = angular u v μ * radialFactor e l μ := rfl
  rw [hrw, hprod]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul, Pi.mul_apply]
  rw [angular_euler, radialFactor_euler]
  have hcast : ((l - μ : ℕ) : ℝ) + (μ : ℝ) = (l : ℝ) := by
    rw [Nat.cast_sub hμ]; ring
  linear_combination (angular u v μ x * radialFactor e l μ x) * hcast
