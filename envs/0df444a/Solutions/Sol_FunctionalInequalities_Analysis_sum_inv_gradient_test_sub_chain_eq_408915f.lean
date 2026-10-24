-- Prove2me | solution 1 for FunctionalInequalities.Analysis.sum_inv_gradient_test_sub_chain_eq_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:17:32.467647+00:00
-- url     : https://prove2.me/submissions/31226c38-097f-413f-914f-2f2ca23b18ac

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_LipschitzBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Piola
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
section InverseMatrixCancellation
open scoped BigOperators
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- Finite inverse-Hessian cancellation for the weak Letwin (2.2) test.
All analytic data are replaced by arbitrary finite matrices and coordinate vectors. -/
 theorem solution {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (hdet : IsUnit A.det)
    (a : ℝ) (b p q r : Fin n → ℝ) :
    (∑ i, ∑ j, A⁻¹ i j * (b j * r i - a * p j * r i + a * B j i)) -
      (∑ i, ∑ j, A⁻¹ i j * (-p j + ∑ k, A j k * q k) * (a * r i)) =
      (∑ i, ∑ j, A⁻¹ i j * b i * r j) +
        a * ((A⁻¹ * B).trace - ∑ i, q i * r i) := by
  have hsymm (i j : Fin n) : A⁻¹ i j = A⁻¹ j i := by
    simpa only [star_trivial] using hA.inv.apply j i
  have hcancel (i : Fin n) :
      (∑ j, A⁻¹ i j * (∑ k, A j k * q k)) = q i := by
    calc
      (∑ j, A⁻¹ i j * (∑ k, A j k * q k)) =
          ∑ k, (∑ j, A⁻¹ i j * A j k) * q k := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = q i := by
        simp only [← Matrix.mul_apply, Matrix.nonsing_inv_mul A hdet]
        simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul]
        simp
  have henergy :
      (∑ i, ∑ j, A⁻¹ i j * b j * r i) =
        ∑ i, ∑ j, A⁻¹ i j * b i * r j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsymm j i]
  have htrace :
      (A⁻¹ * B).trace = ∑ i, ∑ j, A⁻¹ i j * B j i := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  calc
    (∑ i, ∑ j, A⁻¹ i j * (b j * r i - a * p j * r i + a * B j i)) -
        (∑ i, ∑ j, A⁻¹ i j * (-p j + ∑ k, A j k * q k) * (a * r i)) =
        ∑ i, ∑ j,
          (A⁻¹ i j * b j * r i + a * (A⁻¹ i j * B j i) -
            a * (A⁻¹ i j * (∑ k, A j k * q k) * r i)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ i, ∑ j, A⁻¹ i j * b j * r i) +
          a * (∑ i, ∑ j, A⁻¹ i j * B j i) -
          a * (∑ i, q i * r i) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul, hcancel]
    _ = (∑ i, ∑ j, A⁻¹ i j * b i * r j) +
          a * ((A⁻¹ * B).trace - ∑ i, q i * r i) := by
      rw [henergy, ← htrace]
      ring
