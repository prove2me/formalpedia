-- Prove2me | solution 1 for FunctionalInequalities.KLS.covariance_tendsto_one_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:26:07.633311+00:00
-- url     : https://prove2.me/submissions/82fe0a3a-a5aa-4945-aaab-5f19d2dff9d0

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_InverseSqrt
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointClosure
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointComp
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Contraction
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Dissipation
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_MeanValue
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Domain
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_FormDomain
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Laws
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Smoothing
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Form
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_VonNeumann
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Laws
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_CovarianceGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_Slope_Recovery
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_WeakDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Dirichlet
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Relaxation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Core
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
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_FromBorell
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Markov
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_OperatorCore
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Regular_Affine
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Regular_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Closure
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Multiplier
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_BoundedMultiplier
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_L2_Energy
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_Relaxation
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothGradient_Ambient
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothGradient_Intrinsic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Optimal
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
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
import Mathlib.Analysis.Calculus.Deriv.MeanValue
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
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities
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
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
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
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Order.Filter.ENNReal
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor

section
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
section Moments
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
/-- For an isotropic law the raw second moments are `∫ ⟪u, x⟫ ⟪v, x⟫ = ⟪u, v⟫`. -/
theorem FunctionalInequalities.KLS.Isotropic.integral_inner_mul_inner
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ν : ProbabilityMeasure E}
    (hν : Isotropic ν) (u v : E) :
    (∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂(ν : Measure E)) = ⟪u, v⟫ := by
  calc
    (∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂(ν : Measure E)) =
        ∫ x, ⟪u, x - ∫ y, id y ∂(ν : Measure E)⟫ *
          ⟪v, x - ∫ y, id y ∂(ν : Measure E)⟫ ∂(ν : Measure E) := by
      simp [hν.mean_zero]
    _ = ProbabilityTheory.covarianceBilin (ν : Measure E) u v := by
      rw [ProbabilityTheory.covarianceBilin_apply hν.memLp_two]
    _ = ⟪u, v⟫ := by
      rw [← Covariance.operator_inner, hν.covariance_identity]
      simp
end Moments
end
end
end
end

section
noncomputable section
open scoped MatrixOrder Kronecker
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
section Frobenius
open Matrix Finset
open scoped RealInnerProductSpace
omit [Fintype ι] in
theorem FunctionalInequalities.Analysis.continuous_matrixEntries :
    Continuous (matrixEntries : Matrix ι ι ℝ → EuclideanSpace ℝ (ι × ι)) :=
  (PiLp.continuous_toLp 2 (fun _ : ι × ι => ℝ)).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))
end Frobenius
end
end
end
end

section
noncomputable section
open scoped RealInnerProductSpace MatrixOrder
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section OperatorMatrix
open Matrix
variable [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] [DecidableEq ι]
@[simp] theorem FunctionalInequalities.Analysis.operatorOfMatrix_operatorMatrix (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) :
    operatorOfMatrix b (operatorMatrix b T) = T := by
  exact congrArg (fun f : E →ₗ[ℝ] E => f.toContinuousLinearMap)
    ((LinearMap.toMatrixOrthonormal b).symm_apply_apply T.toLinearMap)
/-- Identification of the two coordinate objects: the matrix entry is `operatorEntry`. -/
theorem FunctionalInequalities.Analysis.operatorMatrix_apply_eq_operatorEntry {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    (T : E →L[ℝ] E) (i j : Fin m) : operatorMatrix b T i j = operatorEntry b T i j := by
  rw [operatorMatrix, LinearMap.toMatrixOrthonormal_apply_apply]
  rfl
end OperatorMatrix
end
end
end
end

noncomputable section
open MeasureTheory Set Metric
open scoped RealInnerProductSpace ContDiff
section LT10BWhiteningMoments
open MeasureTheory Set Metric Filter
open scoped Topology RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
private lemma FunctionalInequalities.KLS.integrable_of_ball_support
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] (ν : ProbabilityMeasure E) {R : ℝ}
    (hs : (ν : Measure E) (closedBall (0 : E) R)ᶜ = 0)
    {f : E → F} (hf : Continuous f) :
    Integrable f (ν : Measure E) := by
  have ha : ∀ᵐ x ∂(ν : Measure E), x ∈ closedBall (0 : E) R :=
    ae_iff.mpr hs
  have hi := hf.continuousOn.integrableOn_compact
    (μ := (ν : Measure E)) (isCompact_closedBall (0 : E) R)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem ha] at hi
section FiniteDimensional
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
section MeasurableSpace
variable [MeasurableSpace E] [BorelSpace E]
private lemma FunctionalInequalities.KLS.memLp_two_of_ball_support
    (ν : ProbabilityMeasure E) {R : ℝ}
    (hs : (ν : Measure E) (closedBall (0 : E) R)ᶜ = 0) :
    MemLp id 2 (ν : Measure E) := by
  apply (memLp_two_iff_integrable_sq_norm
    continuous_id.aestronglyMeasurable).2
  exact integrable_of_ball_support ν hs (by fun_prop)
/-- Uniform convergence on the supporting ball gives a bound independent of the law. -/
private lemma FunctionalInequalities.KLS.affine_integral_perturbation
    {lam : ℕ → ProbabilityMeasure E} {R : ℝ}
    (hsupp : ∀ k, (lam k : Measure E) (closedBall (0 : E) R)ᶜ = 0)
    {A : ℕ → E →L[ℝ] E} {c : ℕ → E}
    (hA : Tendsto A atTop (𝓝 1)) (hc : Tendsto c atTop (𝓝 0))
    {f : E → ℝ} (hf : Continuous f) :
    Tendsto
      (fun k => (∫ x, f (A k (x - c k)) ∂(lam k : Measure E)) -
        ∫ x, f x ∂(lam k : Measure E))
      atTop (𝓝 0) := by
  let : CompactSpace (closedBall (0 : E) R) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E) R)
  let F : ((E →L[ℝ] E) × E) → closedBall (0 : E) R → ℝ :=
    fun p x => f (p.1 ((x : E) - p.2))
  have hF : Continuous ↿F := by
    dsimp only [F]
    exact hf.comp (by fun_prop)
  have hu := Continuous.tendstoUniformly F hF (1, 0)
  have hp := hA.prodMk_nhds hc
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := hp.eventually
    ((Metric.tendstoUniformly_iff.mp hu) (ε / 2) (half_pos hε))
  filter_upwards [he] with k hk
  have hb : ∀ᵐ x ∂(lam k : Measure E),
      ‖f (A k (x - c k)) - f x‖ ≤ ε / 2 := by
    filter_upwards [show ∀ᵐ x ∂(lam k : Measure E),
        x ∈ closedBall (0 : E) R from ae_iff.mpr (hsupp k)] with x hx
    have hh := hk ⟨x, hx⟩
    have hh' : dist (f x) (f (A k (x - c k))) < ε / 2 := by
      simpa only [F, sub_zero, one_apply_eq_self] using hh
    rw [dist_comm, dist_eq_norm] at hh'
    exact hh'.le
  have hi : Integrable (fun x => f (A k (x - c k))) (lam k : Measure E) :=
    integrable_of_ball_support (lam k) (hsupp k) (hf.comp (by fun_prop))
  have hj : Integrable f (lam k : Measure E) :=
    integrable_of_ball_support (lam k) (hsupp k) hf
  have hb' := norm_integral_le_of_norm_le_const hb
  rw [integral_sub hi hj, probReal_univ, mul_one] at hb'
  rw [dist_zero_right]
  exact hb'.trans_lt (half_lt_self hε)
private lemma FunctionalInequalities.KLS.mean_tendsto_zero
    {lam : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (hiso : Isotropic μ) {R : ℝ}
    (hsupp : ∀ k, (lam k : Measure E) (closedBall (0 : E) R)ᶜ = 0)
    (hmom : ∀ d : ℕ, d ≤ 4 → ∀ v : Fin d → E,
      Tendsto (fun k => ∫ x, ∏ i, ⟪v i, x⟫ ∂(lam k : Measure E)) atTop
        (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure E)))) :
    Tendsto (fun k => ∫ x, x ∂(lam k : Measure E)) atTop (𝓝 0) := by
  have hv (v : E) :
      Tendsto (fun k => ⟪v, ∫ x, x ∂(lam k : Measure E)⟫)
        atTop (𝓝 (0 : ℝ)) := by
    have h_lam (k : ℕ) :
        (∫ x, ⟪v, x⟫ ∂(lam k : Measure E)) =
          ⟪v, ∫ x, x ∂(lam k : Measure E)⟫ := by
      exact (innerSL ℝ v).integral_comp_comm
        (integrable_of_ball_support (lam k) (hsupp k) continuous_id)
    have h_mu : (∫ x, ⟪v, x⟫ ∂(μ : Measure E)) = 0 := by
      have hi : Integrable (fun x : E => x) (μ : Measure E) :=
        hiso.memLp_two.integrable (by norm_num)
      have hh := (innerSL ℝ v).integral_comp_comm hi
      change (∫ x, ⟪v, x⟫ ∂(μ : Measure E)) =
        ⟪v, ∫ x, x ∂(μ : Measure E)⟫ at hh
      rw [hh, hiso.mean_zero, inner_zero_right]
    simpa only [Fin.prod_univ_one, h_lam, h_mu] using
      hmom 1 (by norm_num) (fun _ => v)
  let b := stdOrthonormalBasis ℝ E
  have h := tendsto_finsetSum Finset.univ
    (fun i _ => (hv (b i)).smul_const (b i))
  simpa only [b.sum_repr', zero_smul, Finset.sum_const_zero] using h
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities.KLS in
 lemma solution
    {lam : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (hiso : FunctionalInequalities.KLS.Isotropic μ) {R : ℝ}
    (hsupp : ∀ k, (lam k : Measure E) (closedBall (0 : E) R)ᶜ = 0)
    (hmom : ∀ d : ℕ, d ≤ 4 → ∀ v : Fin d → E,
      Tendsto (fun k => ∫ x, ∏ i, ⟪v i, x⟫ ∂(lam k : Measure E)) atTop
        (𝓝 (∫ x, ∏ i, ⟪v i, x⟫ ∂(μ : Measure E)))) :
    Tendsto (fun k => FunctionalInequalities.Covariance.operator (lam k : Measure E)) atTop (𝓝 1) := by
  let m : ℕ → E := fun k => ∫ x, x ∂(lam k : Measure E)
  have hm : Tendsto m atTop (𝓝 0) :=
    mean_tendsto_zero hiso hsupp hmom
  have hcenter (u v : E) :
      Tendsto
        (fun k => ∫ x, ⟪u, x - m k⟫ * ⟪v, x - m k⟫
          ∂(lam k : Measure E)) atTop (𝓝 ⟪u, v⟫) := by
    have hr :
        Tendsto (fun k => ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂(lam k : Measure E))
          atTop (𝓝 ⟪u, v⟫) := by
      simpa [Fin.prod_univ_two, hiso.integral_inner_mul_inner] using
        hmom 2 (by norm_num) ![u, v]
    have hp := affine_integral_perturbation hsupp
      (A := fun _ => (1 : E →L[ℝ] E)) tendsto_const_nhds hm
      (f := fun x => ⟪u, x⟫ * ⟪v, x⟫) (by fun_prop)
    simpa only [one_apply_eq_self, sub_add_cancel, zero_add] using hp.add hr
  have hcoord (u v : E) :
      Tendsto (fun k => ⟪u, FunctionalInequalities.Covariance.operator (lam k : Measure E) v⟫)
        atTop (𝓝 ⟪u, v⟫) := by
    have he (k : ℕ) :
        ⟪u, FunctionalInequalities.Covariance.operator (lam k : Measure E) v⟫ =
          ∫ x, ⟪v, x - m k⟫ * ⟪u, x - m k⟫ ∂(lam k : Measure E) := by
      rw [real_inner_comm (FunctionalInequalities.Covariance.operator (lam k : Measure E) v) u,
        FunctionalInequalities.Covariance.operator_inner,
        ProbabilityTheory.covarianceBilin_apply
          (memLp_two_of_ball_support (lam k) (hsupp k))]
      rfl
    have h := hcenter v u
    rw [real_inner_comm u v] at h
    simpa only [he] using h
  let b := stdOrthonormalBasis ℝ E
  have hM :
      Tendsto (fun k => FunctionalInequalities.Analysis.operatorMatrix b (FunctionalInequalities.Covariance.operator (lam k : Measure E)))
        atTop (𝓝 (FunctionalInequalities.Analysis.operatorMatrix b (1 : E →L[ℝ] E))) :=
    tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => by
      simpa only [FunctionalInequalities.Analysis.operatorMatrix_apply_eq_operatorEntry,
        FunctionalInequalities.Analysis.operatorEntry, one_apply_eq_self] using hcoord (b i) (b j)
  have hh := ((FunctionalInequalities.Analysis.operatorOfMatrixL b).continuous.tendsto _).comp
    ((FunctionalInequalities.Analysis.continuous_matrixEntries.tendsto _).comp hM)
  simpa only [Function.comp_def, FunctionalInequalities.Analysis.operatorOfMatrixL_matrixEntries,
    FunctionalInequalities.Analysis.operatorOfMatrix_operatorMatrix] using hh
