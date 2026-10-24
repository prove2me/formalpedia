-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.norm_coordTensor_taylorTensor_inner_sq_le_of_basis_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:50:53.935611+00:00
-- url     : https://prove2.me/submissions/75a06646-0fd0-44a1-86c4-4319a34f1f76

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Variance
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_taylorTensor_inner_eq_cumulant_408915f

section
noncomputable section
open Finset
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Tensor
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem FunctionalInequalities.Analysis.Tensor.coordTensor_apply {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) (i : Fin k → Fin n) :
    coordTensor b Φ i = Φ (fun j => b (i j)) := by
  rfl
end
end
end
end
end

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section CumulantEstimates
omit [CompleteSpace E]
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- **Linear-function step in an arbitrary orthonormal basis** (BKL p. 30): the special case
`norm_coordTensor_taylorTensor_inner_sq_le` with `stdOrthonormalBasis ℝ E` replaced by any orthonormal
basis `bE`. -/
theorem solution (μ : Measure E) [IsProbabilityMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {m : ℕ}
    (bE : OrthonormalBasis (Fin m) ℝ E) {d : ℕ} {b : ℝ}
    (hR : ∀ u : E, ∑ J : Fin d → Fin m,
      FunctionalInequalities.Analysis.BakryEmery.cumulant μ (d + 1) (Fin.cons u fun k => bE (J k)) ^ 2 ≤ b * ‖u‖ ^ 2) (v : E) :
    ‖FunctionalInequalities.Analysis.Tensor.coordTensor bE (FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ (fun x => ⟪v, x⟫) d)‖ ^ 2 ≤
      b / (d.factorial : ℝ) ^ 2 * ‖v‖ ^ 2 := by
    have hcoord :
        ∀ J : Fin d → Fin m,
          (FunctionalInequalities.Analysis.Tensor.coordTensor (bE)
              (FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ (fun x => ⟪v, x⟫) d)).ofLp J =
            (d.factorial : ℝ)⁻¹ *
              FunctionalInequalities.Analysis.BakryEmery.cumulant μ (d + 1)
                (Fin.cons v (fun k => bE (J k))) := by
      intro J
      simp [FunctionalInequalities.Analysis.Tensor.coordTensor_apply, FunctionalInequalities.Analysis.BakryEmery.taylorTensor_inner_eq_cumulant_408915f, hexp]
    rw [EuclideanSpace.norm_sq_eq]
    calc
      ∑ J : Fin d → Fin m,
          ‖(FunctionalInequalities.Analysis.Tensor.coordTensor (bE)
              (FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ (fun x => ⟪v, x⟫) d)).ofLp J‖ ^ 2 =
        ((d.factorial : ℝ)⁻¹) ^ 2 *
          ∑ J : Fin d → Fin m,
            FunctionalInequalities.Analysis.BakryEmery.cumulant μ (d + 1)
              (Fin.cons v (fun k => bE (J k))) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro J hJ
        rw [hcoord J, norm_mul]
        simp [Real.norm_eq_abs, sq_abs, mul_pow]
      _ ≤ ((d.factorial : ℝ)⁻¹) ^ 2 * (b * ‖v‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left (hR v) (sq_nonneg _)
      _ = b / (d.factorial : ℝ) ^ 2 * ‖v‖ ^ 2 := by
        simp [div_eq_mul_inv, inv_pow]
        ring
