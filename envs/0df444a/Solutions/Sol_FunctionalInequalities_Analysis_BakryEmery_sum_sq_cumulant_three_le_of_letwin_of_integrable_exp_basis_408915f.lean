-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.sum_sq_cumulant_three_le_of_letwin_of_integrable_exp_basis_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:51:36.116546+00:00
-- url     : https://prove2.me/submissions/db25a172-c92d-4f80-ad2c-f8537871a364

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_LocalDerivatives
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_sum_sq_cumulant_three_le_of_letwin_of_integrable_exp_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_coordTensor_sq_eq_408915f

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

open MeasureTheory Filter Topology
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem FunctionalInequalities.Analysis.BakryEmery.sum_pair_eq_sum_tensor {m : ℕ}
    (b : OrthonormalBasis (Fin m) ℝ E)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ) :
    (∑ j, ∑ k, T ![b j, b k] ^ 2) =
      ∑ J : Fin 2 → Fin m, Analysis.Tensor.coordTensor b T J ^ 2 := by
  classical
  calc
    (∑ j, ∑ k, T ![b j, b k] ^ 2) =
        ∑ q : Fin m × Fin m, T ![b q.1, b q.2] ^ 2 :=
      (Fintype.sum_prod_type (fun q : Fin m × Fin m => T ![b q.1, b q.2] ^ 2)).symm
    _ = ∑ q : Fin m × Fin m,
        Analysis.Tensor.coordTensor b T ((finTwoArrowEquiv (Fin m)).symm q) ^ 2 := by
      apply Finset.sum_congr rfl
      intro q _hq
      rw [Analysis.Tensor.coordTensor_apply, finTwoArrowEquiv_symm_apply]
      have heq : (fun i => b (![q.1, q.2] i)) = ![b q.1, b q.2] := by
        ext i
        fin_cases i <;> rfl
      rw [heq]
    _ = _ := (finTwoArrowEquiv (Fin m)).symm.sum_comp
      (fun J => Analysis.Tensor.coordTensor b T J ^ 2)
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- The same bound in any orthonormal basis (Hilbert–Schmidt norm is basis independent). -/
theorem solution (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    (hc : ∀ v : E, ∫ x, ⟪v, x⟫ ∂μ = 0)
    (hiso : ∀ v w : E, ∫ x, ⟪v, x⟫ * ⟪w, x⟫ ∂μ = ⟪v, w⟫)
    (hL : FunctionalInequalities.Analysis.BakryEmery.LetwinQuadraticBound μ) {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E) (u : E) :
    ∑ j, ∑ k, FunctionalInequalities.Analysis.BakryEmery.cumulant μ 3 ![u, b j, b k] ^ 2 ≤ 8 * ‖u‖ ^ 2 := by
  have hcons (a b : E) : Fin.cons u ![a, b] = ![u, a, b] := by
    ext i
    fin_cases i <;> rfl
  let T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ :=
    (FunctionalInequalities.Analysis.BakryEmery.cumulant μ 3).curryLeft u
  have hb : (∑ j, ∑ k, FunctionalInequalities.Analysis.BakryEmery.cumulant μ 3 ![u, b j, b k] ^ 2) =
      ∑ J : Fin 2 → Fin m, FunctionalInequalities.Analysis.Tensor.coordTensor b T J ^ 2 := by
    simpa only [T, ContinuousMultilinearMap.curryLeft_apply, hcons] using sum_pair_eq_sum_tensor b T
  have hs : (∑ j, ∑ k, FunctionalInequalities.Analysis.BakryEmery.cumulant μ 3
      ![u, stdOrthonormalBasis ℝ E j, stdOrthonormalBasis ℝ E k] ^ 2) =
      ∑ J : Fin 2 → Fin (Module.finrank ℝ E),
        FunctionalInequalities.Analysis.Tensor.coordTensor (stdOrthonormalBasis ℝ E) T J ^ 2 := by
    simpa only [T, ContinuousMultilinearMap.curryLeft_apply, hcons] using
      sum_pair_eq_sum_tensor (stdOrthonormalBasis ℝ E) T
  rw [hb, FunctionalInequalities.Analysis.Tensor.sum_coordTensor_sq_eq_408915f b (stdOrthonormalBasis ℝ E) T, ← hs]
  exact FunctionalInequalities.Analysis.BakryEmery.sum_sq_cumulant_three_le_of_letwin_of_integrable_exp_408915f μ hr hexp hc hiso hL u
