-- Prove2me | solution 1 for FunctionalInequalities.Analysis.smooth_test_derivative_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:17:57.927376+00:00
-- url     : https://prove2.me/submissions/de0a2585-c3bc-45cf-b6a3-aad7de70b1b1

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
section GeneratorIdentities
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
open FunctionalInequalities.Probability.Stein
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
 lemma solution {n : ℕ}
    {u a f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (ha : ContDiff ℝ 1 a)
    (hf : ContDiff ℝ 2 f) (i j : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) :
    FunctionalInequalities.Analysis.coord (FunctionalInequalities.Analysis.weightedTest u a f i) j x =
      Real.exp (-u x) *
        (FunctionalInequalities.Analysis.coord a j x * FunctionalInequalities.Analysis.coord f i x -
          a x * FunctionalInequalities.Analysis.coord u j x * FunctionalInequalities.Analysis.coord f i x +
          a x * FunctionalInequalities.Probability.Stein.hessianMatrix f x j i) := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf.fderiv_right (by norm_num)
  have hfdx := (hfd.differentiable one_ne_zero).differentiableAt (x := x)
  have hc :
      DifferentiableAt ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ i) x :=
    (differentiable_const (EuclideanSpace.basisFun (Fin n) ℝ i) :
      Differentiable ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ i)).differentiableAt
  have hcomponent : DifferentiableAt ℝ (FunctionalInequalities.Analysis.coord f i) x :=
    hfdx.clm_apply hc
  have hcoord :
      FunctionalInequalities.Analysis.coord (FunctionalInequalities.Analysis.coord f i) j x = FunctionalInequalities.Probability.Stein.hessianMatrix f x j i := by
    have he := congrArg
      (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
        L (EuclideanSpace.basisFun (Fin n) ℝ j))
      (fderiv_clm_apply hfdx hc)
    change
      fderiv ℝ
        (fun y => fderiv ℝ f y (EuclideanSpace.basisFun (Fin n) ℝ i)) x
        (EuclideanSpace.basisFun (Fin n) ℝ j) =
          FunctionalInequalities.Probability.Stein.hessianMatrix f x j i
    simpa [FunctionalInequalities.Probability.Stein.hessianMatrix, bilinearIteratedFDerivTwo] using he
  have hux : DifferentiableAt ℝ u x :=
    hu.differentiable one_ne_zero x
  have hax : DifferentiableAt ℝ a x :=
    ha.differentiable one_ne_zero x
  have he :
      fderiv ℝ (FunctionalInequalities.Analysis.weightedTest u a f i) x =
        (a x * Real.exp (-u x)) • fderiv ℝ (FunctionalInequalities.Analysis.coord f i) x +
          FunctionalInequalities.Analysis.coord f i x •
            (a x • (Real.exp (-u x) • (-fderiv ℝ u x)) +
              Real.exp (-u x) • fderiv ℝ a x) :=
    ((hax.hasFDerivAt.mul hux.hasFDerivAt.neg.exp).mul
      hcomponent.hasFDerivAt).fderiv
  change fderiv ℝ (FunctionalInequalities.Analysis.weightedTest u a f i) x
    (EuclideanSpace.basisFun (Fin n) ℝ j) = _
  rw [he]
  simp only [_root_.add_apply, _root_.smul_apply, _root_.neg_apply, smul_eq_mul]
  change
    (a x * Real.exp (-u x)) * FunctionalInequalities.Analysis.coord (FunctionalInequalities.Analysis.coord f i) j x +
      FunctionalInequalities.Analysis.coord f i x *
        (a x * (Real.exp (-u x) * (-FunctionalInequalities.Analysis.coord u j x)) +
          Real.exp (-u x) * FunctionalInequalities.Analysis.coord a j x) = _
  rw [hcoord]
  ring
