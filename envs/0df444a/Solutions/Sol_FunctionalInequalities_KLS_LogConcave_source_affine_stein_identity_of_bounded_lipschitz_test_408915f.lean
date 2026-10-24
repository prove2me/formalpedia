-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.source_affine_stein_identity_of_bounded_lipschitz_test_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:34:40.918761+00:00
-- url     : https://prove2.me/submissions/3febde67-2a86-4d2c-8b62-a5fbd362bfef

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_LinearEquiv
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Translation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_WeakDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Comparison
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Quadratic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Closable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Isotropic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Translation
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Statement
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_Comparison
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_CovarianceGradient_Intrinsic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_L2_Energy
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_LipschitzGradient_Comparison
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_Relaxation
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothGradient_Ambient
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothGradient_Intrinsic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Optimal
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_IntrinsicTranslation
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Stein_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
import Mathlib
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Order.Filter.ENNReal
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_source_stein_identity_of_bounded_lipschitz_test_408915f

section
noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
noncomputable section
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
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
theorem FunctionalInequalities.Analysis.BakryEmery.gradient_comp_affine {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (S : E →L[ℝ] F) (z : F) {f : F → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f (S x + z)) :
    gradient (fun y => f (S y + z)) x = S.adjoint (gradient f (S x + z)) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, ContinuousLinearMap.adjoint_inner_left, inner_gradient_left]
  exact congrArg (fun T : E →L[ℝ] ℝ => T v)
    (hf.hasFDerivAt.comp x (S.hasFDerivAt.add_const z)).fderiv
end
end
end
end
end
end

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
set_option maxHeartbeats 600000 in
theorem FunctionalInequalities.KLS.LogConcave.source_directional_stein_identity_of_bounded_lipschitz_test {n : ℕ}
    {u f : EuclideanSpace ℝ (Fin n) → ℝ} {L G Lf : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u))
    (hnorm : (∫ y, Real.exp (-u y) ∂volume) = 1)
    (hf : ContDiff ℝ 1 f) (hfLip : LipschitzWith Lf f)
    (C : ℝ) (hbound : ∀ x, ‖f x‖ ≤ C) (v : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y => ⟪gradient u y, v⟫ * f (gradient u y))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
    Integrable (fun y => ⟪v, action (hessianMatrix u y) (gradient f (gradient u y))⟫)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
    (∫ y, ⟪gradient u y, v⟫ * f (gradient u y)
      ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
      ∫ y, ⟪v, action (hessianMatrix u y) (gradient f (gradient u y))⟫
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) := by
  classical
  let mu : Measure (EuclideanSpace ℝ (Fin n)) := volume.tilted (-u)
  let A (i : Fin n) (y : EuclideanSpace ℝ (Fin n)) := gradient u y i * f (gradient u y)
  let B (i : Fin n) (y : EuclideanSpace ℝ (Fin n)) :=
    ∑ j, hessianMatrix u y i j * gradient f (gradient u y) j
  have hp (i : Fin n) := source_stein_identity_of_bounded_lipschitz_test_408915f hu hL hG hnorm hf hfLip C hbound i
  have hA : Integrable (fun y => ∑ i, v i * A i y) mu :=
    integrable_finsetSum Finset.univ fun i _ => (hp i).1.const_mul (v i)
  have hB : Integrable (fun y => ∑ i, v i * B i y) mu :=
    integrable_finsetSum Finset.univ fun i _ => (hp i).2.1.const_mul (v i)
  have heqA (y : EuclideanSpace ℝ (Fin n)) : (∑ i, v i * A i y) =
      ⟪gradient u y, v⟫ * f (gradient u y) := by
    simp only [PiLp.inner_apply, Real.inner_apply, Finset.sum_mul, A]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have heqB (y : EuclideanSpace ℝ (Fin n)) : (∑ i, v i * B i y) =
      ⟪v, action (hessianMatrix u y) (gradient f (gradient u y))⟫ := by
    simp only [PiLp.inner_apply, Real.inner_apply, action, Matrix.mulVec, dotProduct, B]
  refine ⟨hA.congr (ae_of_all _ heqA), hB.congr (ae_of_all _ heqB), ?_⟩
  calc
    _ = ∫ y, ∑ i, v i * A i y ∂mu := (integral_congr_ae (ae_of_all _ heqA)).symm
    _ = ∑ i, v i * ∫ y, A i y ∂mu := by
      rw [integral_finsetSum Finset.univ (fun i _ => (hp i).1.const_mul (v i))]
      simp only [integral_const_mul, A, mu]
    _ = ∑ i, v i * ∫ y, B i y ∂mu := by
      apply Finset.sum_congr rfl
      intro i _
      rw [(hp i).2.2]
    _ = ∫ y, ∑ i, v i * B i y ∂mu := by
      rw [integral_finsetSum Finset.univ (fun i _ => (hp i).2.1.const_mul (v i))]
      simp only [integral_const_mul, B, mu]
    _ = _ := integral_congr_ae (ae_of_all _ heqB)
end
end
end
end
noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave in
set_option maxHeartbeats 600000 in
theorem solution {n : ℕ}
    {u h : EuclideanSpace ℝ (Fin n) → ℝ} {L G Lh : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u)
    (hG : LipschitzWith G (gradient u))
    (hnorm : (∫ y, Real.exp (-u y) ∂volume) = 1)
    (hh : ContDiff ℝ 1 h) (hhLip : LipschitzWith Lh h)
    (C : ℝ) (hbound : ∀ x, ‖h x‖ ≤ C)
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (z v : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y => ⟪S (gradient u y), v⟫ * h (S (gradient u y) + z))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
    Integrable (fun y => ⟪S.adjoint v,
      FunctionalInequalities.Probability.Stein.action (FunctionalInequalities.Probability.Stein.hessianMatrix u y) (S.adjoint (gradient h (S (gradient u y) + z)))⟫)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
    (∫ y, ⟪S (gradient u y), v⟫ * h (S (gradient u y) + z)
      ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
      ∫ y, ⟪S.adjoint v,
        FunctionalInequalities.Probability.Stein.action (FunctionalInequalities.Probability.Stein.hessianMatrix u y) (S.adjoint (gradient h (S (gradient u y) + z)))⟫
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) := by
  have hf : ContDiff ℝ 1 (fun x => h (S x + z)) := hh.comp (S.contDiff.add contDiff_const)
  have hp := FunctionalInequalities.KLS.LogConcave.source_directional_stein_identity_of_bounded_lipschitz_test hu hL hG hnorm
    hf (hhLip.comp (S.lipschitz.add (LipschitzWith.const z))) C (fun x => hbound (S x + z)) (S.adjoint v)
  have hleft (y : EuclideanSpace ℝ (Fin n)) :
      ⟪gradient u y, S.adjoint v⟫ * h (S (gradient u y) + z) =
      ⟪S (gradient u y), v⟫ * h (S (gradient u y) + z) := by
    rw [S.adjoint_inner_right]
  have hright (y : EuclideanSpace ℝ (Fin n)) :
      ⟪S.adjoint v, FunctionalInequalities.Probability.Stein.action (FunctionalInequalities.Probability.Stein.hessianMatrix u y) (gradient (fun x => h (S x + z)) (gradient u y))⟫ =
      ⟪S.adjoint v, FunctionalInequalities.Probability.Stein.action (FunctionalInequalities.Probability.Stein.hessianMatrix u y) (S.adjoint (gradient h (S (gradient u y) + z)))⟫ := by
    rw [FunctionalInequalities.Analysis.BakryEmery.gradient_comp_affine S z (hh.differentiable one_ne_zero _)]
  refine ⟨hp.1.congr (ae_of_all _ hleft), hp.2.1.congr (ae_of_all _ hright), ?_⟩
  exact (integral_congr_ae (ae_of_all _ hleft)).symm.trans (hp.2.2.trans
    (integral_congr_ae (ae_of_all _ hright)))
