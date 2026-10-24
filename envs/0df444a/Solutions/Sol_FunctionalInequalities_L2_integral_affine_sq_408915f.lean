-- Prove2me | solution 1 for FunctionalInequalities.L2.integral_affine_sq_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:45:23.248612+00:00
-- url     : https://prove2.me/submissions/41270d20-7b9e-4900-9d5d-7a4872125378

import Definitions.Def_KLS408915f_FunctionalInequalities_L2_AffineDecomposition
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.L2
end FunctionalInequalities.L2
open FunctionalInequalities FunctionalInequalities.L2
section AffineOrthPart
variable {n : ℕ}
namespace FunctionalInequalities.L2
end FunctionalInequalities.L2
open FunctionalInequalities.L2 in
/-- **Square integral of an affine function** under a centered law with identity covariance. -/
theorem solution (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    (c : ℝ) (a : Fin n → ℝ) :
    ∫ x, (c + ∑ j, a j * ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) ^ 2 ∂μ =
      c ^ 2 + ∑ j, a j ^ 2 := by
    classical
    let v : EuclideanSpace ℝ (Fin n) :=
      ∑ j, a j • EuclideanSpace.basisFun (Fin n) ℝ j
    have hsum (x : EuclideanSpace ℝ (Fin n)) :
        ∑ j, a j * ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ = ⟪v, x⟫ := by
      simp [v, sum_inner, inner_smul_left]
    have hlin_mem : MemLp (fun x : EuclideanSpace ℝ (Fin n) => ⟪v, x⟫) 2 μ := by
      simpa [Function.comp_def] using (innerSL ℝ v).comp_memLp' hμ2
    have hlin_int : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ⟪v, x⟫) μ :=
      hlin_mem.integrable one_le_two
    have hprod_int :
        Integrable
          (fun x : EuclideanSpace ℝ (Fin n) => ⟪v, x⟫ * ⟪v, x⟫) μ := by
      exact hlin_mem.integrable_mul hlin_mem
    have hscaled_int :
        Integrable
          (fun x : EuclideanSpace ℝ (Fin n) => 2 * c * ⟪v, x⟫) μ := by
      exact hlin_int.const_mul (2 * c)
    have hzero : ∫ x, ⟪v, x⟫ ∂μ = 0 := by
      simpa [Function.comp_def, hμ0] using
        (innerSL ℝ v).integral_comp_comm (hμ2.integrable one_le_two)
    have hvpoint (x : Fin n) : v.ofLp x = a x := by
      simp [v, Pi.single_apply]
    have hvv : ⟪v, v⟫ = ∑ j, a j ^ 2 := by
      rw [real_inner_self_eq_norm_sq, EuclideanSpace.norm_sq_eq]
      apply Finset.sum_congr rfl
      intro x hx
      rw [hvpoint x]
      simp [Real.norm_eq_abs]
    have hfun :
        (fun x => (c + ∑ j, a j * ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) ^ 2) =
          (fun x => c ^ 2 + (2 * c * ⟪v, x⟫ + ⟪v, x⟫ * ⟪v, x⟫)) := by
      funext x
      rw [hsum]
      ring
    have hconst : ∫ x, c ^ 2 ∂μ = c ^ 2 := by
      simp
    have hlin : ∫ x, 2 * c * ⟪v, x⟫ ∂μ = 0 := by
      rw [integral_const_mul, hzero, mul_zero]
    calc
      ∫ x, (c + ∑ j, a j * ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) ^ 2 ∂μ =
          ∫ x, c ^ 2 + (2 * c * ⟪v, x⟫ + ⟪v, x⟫ * ⟪v, x⟫) ∂μ := by
            rw [hfun]
      _ = (∫ x, c ^ 2 ∂μ) +
            ∫ x, (2 * c * ⟪v, x⟫ + ⟪v, x⟫ * ⟪v, x⟫) ∂μ := by
            exact integral_add (integrable_const _) (hscaled_int.add hprod_int)
      _ = c ^ 2 + ∑ j, a j ^ 2 := by
            rw [integral_add hscaled_int hprod_int, hconst, hlin, hμcov v v, hvv]
            ring
