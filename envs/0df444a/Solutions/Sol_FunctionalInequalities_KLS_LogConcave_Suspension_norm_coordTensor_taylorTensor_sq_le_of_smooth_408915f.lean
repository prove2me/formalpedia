-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.norm_coordTensor_taylorTensor_sq_le_of_smooth_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T18:02:57.325077+00:00
-- url     : https://prove2.me/submissions/86079b09-9128-4b4f-b4da-ac6499f0d4a3

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
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Derivatives
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Law
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
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Regular_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Closure
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Multiplier
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_AffineDecomposition
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
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_Laplace
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
import Mathlib.Algebra.Order.Chebyshev
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
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
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
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Order.Filter.ENNReal
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.MGFAnalytic
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
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_exists_norm_coordTensor_taylorTensor_le_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_taylorTensor_add_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_taylorTensor_const_mul_408915f
import Theorems.Thm_FunctionalInequalities_KLS_RegularPotential_integrable_exp_mul_norm_408915f
import Theorems.Thm_FunctionalInequalities_L2_contDiff_affineOrthPart_408915f
import Theorems.Thm_FunctionalInequalities_L2_eLpNorm_le_eLpNorm_of_integral_sq_le_408915f
import Theorems.Thm_FunctionalInequalities_L2_integral_affineOrthPart_408915f
import Theorems.Thm_FunctionalInequalities_L2_integral_affineOrthPart_sq_le_408915f
import Theorems.Thm_FunctionalInequalities_L2_integral_inner_mul_affineOrthPart_408915f
import Theorems.Thm_FunctionalInequalities_L2_memLp_affineOrthPart_408915f
import Theorems.Thm_FunctionalInequalities_L2_sub_affineOrthPart_eq_408915f

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

section
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
/-- **Contraction towards the affine-orthogonal functions**: if `f ∈ L²` is centered and orthogonal
to the linear functions, then `‖f - g̃‖₂ ≤ ‖f - g‖₂`. -/
theorem FunctionalInequalities.L2.eLpNorm_sub_affineOrthPart_le (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 μ) (hf0 : ∫ x, f x ∂μ = 0)
    (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂μ = 0) (hg : MemLp g 2 μ) :
    eLpNorm (f - affineOrthPart μ g) 2 μ ≤ eLpNorm (f - g) 2 μ := by
  rw [sub_affineOrthPart_eq_408915f μ hμ2 hf hf0 hfx hg]
  have hfg : MemLp (f - g) 2 μ := hf.sub hg
  refine eLpNorm_le_eLpNorm_of_integral_sq_le_408915f
      (memLp_affineOrthPart_408915f μ hμ2 hfg) hfg ?_
  exact integral_affineOrthPart_sq_le_408915f μ hμ2 hμ0 hμcov hfg
end AffineOrthPart
end
end
end

open MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace
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
section
namespace FunctionalInequalities.KLS.LogConcave.Suspension
end FunctionalInequalities.KLS.LogConcave.Suspension
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.Suspension
open scoped ContDiff
section NormedSpace
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.compact_c2_hessian_bounded
    {g : E → F} (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g) :
    ∃ M : ℝ, ∀ x : E, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ M := by
  have hd : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have hcontinuous : Continuous (fderiv ℝ (fderiv ℝ g)) :=
    hd.continuous_fderiv one_ne_zero
  have hnorm : Continuous (fun x : E => ‖fderiv ℝ (fderiv ℝ g) x‖) :=
    Continuous.norm (E := E →L[ℝ] E →L[ℝ] F) hcontinuous
  obtain ⟨M, hM⟩ := hc.isCompact.exists_bound_of_continuousOn hnorm.continuousOn
  refine ⟨max M 0, fun x => ?_⟩
  by_cases hx : x ∈ tsupport g
  · have hbound : ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ M := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (fderiv ℝ (fderiv ℝ g) x))]
        using hM x hx
    exact hbound.trans (le_max_left M 0)
  · have hx1 : x ∉ tsupport (fderiv ℝ g) :=
      fun h => hx (tsupport_fderiv_subset ℝ h)
    rw [fderiv_of_notMem_tsupport ℝ hx1, ContinuousLinearMap.opNorm_zero]
    exact le_max_right M 0
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.smooth_compact_hessian_bounded
    {g : E → F} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ∃ M : ℝ, ∀ x : E, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ M := by
  have hg2 : ContDiff ℝ 2 g := hg.of_le (WithTop.coe_le_coe.mpr le_top)
  exact compact_c2_hessian_bounded hg2 hc
end NormedSpace
set_option autoImplicit false
open MeasureTheory FunctionalInequalities.L2
open scoped ContDiff RealInnerProductSpace
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.smooth_affineOrthPart {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (affineOrthPart μ ψ) := by
  unfold affineOrthPart
  apply (hψ.sub contDiff_const).sub
  apply ContDiff.sum
  intro j _
  exact contDiff_const.mul (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ j)).contDiff
/-- Genuine smooth compact-support inputs yield projected L2 approximants in the actual
affine-orthogonal subspace. The projected function itself need not have compact support. -/
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.exists_projected_smooth_approx {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂μ = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      HasCompactSupport ψ ∧ ContDiff ℝ ∞ ψ ∧
      MemLp ψ 2 μ ∧ ContDiff ℝ ∞ (affineOrthPart μ ψ) ∧
      MemLp (affineOrthPart μ ψ) 2 μ ∧
      (∫ x, affineOrthPart μ ψ x ∂μ) = 0 ∧
      (∀ u, ∫ x, ⟪u, x⟫ * affineOrthPart μ ψ x ∂μ = 0) ∧
      eLpNorm (f - affineOrthPart μ ψ) 2 μ ≤ ENNReal.ofReal ε := by
  obtain ⟨ψ, hψsupp, hψsmooth, hψapprox⟩ :=
    hf.exist_eLpNorm_sub_le (by norm_num : (2 : ENNReal) ≠ ⊤) one_le_two hε
  have hψ2 : MemLp ψ 2 μ := hψsmooth.continuous.memLp_of_hasCompactSupport hψsupp
  refine ⟨ψ, hψsupp, hψsmooth, hψ2, smooth_affineOrthPart μ hψsmooth,
    memLp_affineOrthPart_408915f μ hμ2 hψ2, integral_affineOrthPart_408915f μ hμ2 hμ0 hψ2,
    integral_inner_mul_affineOrthPart_408915f μ hμ2 hμ0 hμcov hψ2, ?_⟩
  exact (eLpNorm_sub_affineOrthPart_le μ hμ2 hμ0 hμcov hf hf0 hfx hψ2).trans hψapprox
/-- Actual smooth-infinity bounded-Hessian affine-orthogonal tests are dense in the original
affine-orthogonal L2 subspace. Compact support is used before affine projection. -/
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.exists_smooth_bounded_hessian_approx {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂μ = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ g ∧
      (∃ M : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ M) ∧ MemLp g 2 μ ∧
      (∫ x, g x ∂μ) = 0 ∧ (∀ u, ∫ x, ⟪u, x⟫ * g x ∂μ = 0) ∧
      eLpNorm (f - g) 2 μ ≤ ENNReal.ofReal ε := by
  obtain ⟨ψ, hψsupp, hψsmooth, _, hgsmooth, hg2, hg0, hgorth, happrox⟩ :=
    exists_projected_smooth_approx μ hμ2 hμ0 hμcov hf hf0 hfx hε
  obtain ⟨M, hM⟩ := smooth_compact_hessian_bounded hψsmooth hψsupp
  have hψC2 : ContDiff ℝ 2 ψ := hψsmooth.of_le (WithTop.coe_le_coe.mpr le_top)
  refine ⟨affineOrthPart μ ψ, hgsmooth, ⟨M, ?_⟩, hg2, hg0, hgorth, happrox⟩
  intro x
  rw [(contDiff_affineOrthPart_408915f μ hψC2).2 x]
  exact hM x
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.hessian_const_mul {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : ContDiff ℝ ∞ g) (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fderiv ℝ (fun y => c * g y)) x = c • fderiv ℝ (fderiv ℝ g) x := by
  have hdg : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
  have heq : fderiv ℝ (fun y => c * g y) = fun y => c • fderiv ℝ g y := by
    funext y
    have heqf : (fun y => c * g y) = c • g := rfl
    rw [heqf]
    exact (((hg.differentiable (by simp)).differentiableAt.hasFDerivAt).const_smul c).fderiv
  rw [heq]
  exact (((hdg.differentiable (by simp)).differentiableAt.hasFDerivAt).const_smul c).fderiv
/-- A genuine nonzero smooth affine-orthogonal L2 test can be normalized to all of (108),
retaining smooth infinity and an actual Hessian bound. -/
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.normalize_smooth_test {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ ∞ g)
    (hM : ∃ M : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ M)
    (hg2 : MemLp g 2 μ) (hg0 : ∫ x, g x ∂μ = 0)
    (hgorth : ∀ u, ∫ x, ⟪u, x⟫ * g x ∂μ = 0)
    (hpos : 0 < ∫ x, g x ^ 2 ∂μ) :
    let s : ℝ := Real.sqrt (∫ x, g x ^ 2 ∂μ)
    let q : EuclideanSpace ℝ (Fin n) → ℝ := fun x => g x / s
    ContDiff ℝ ∞ q ∧ (∃ B : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ q) x‖ ≤ B) ∧
      MemLp q 2 μ ∧ (∫ x, q x ∂μ) = 0 ∧ (∫ x, q x ^ 2 ∂μ) = 1 ∧
      (∀ u, ∫ x, ⟪u, x⟫ * q x ∂μ = 0) := by
  dsimp only
  let s : ℝ := Real.sqrt (∫ x, g x ^ 2 ∂μ)
  have hs : 0 < s := Real.sqrt_pos.2 hpos
  have hs2 : s ^ 2 = ∫ x, g x ^ 2 ∂μ := Real.sq_sqrt hpos.le
  obtain ⟨M, hM⟩ := hM
  have hq2 : MemLp (fun x => g x / s) 2 μ := by
    simpa only [div_eq_mul_inv] using hg2.mul_const s⁻¹
  refine ⟨hg.div_const s, ⟨|s⁻¹| * M, ?_⟩, hq2, ?_, ?_, ?_⟩
  · intro x
    have heq : (fun x => g x / s) = fun x => s⁻¹ * g x := by
      funext x
      simp only [div_eq_mul_inv, mul_comm]
    rw [heq, hessian_const_mul hg]
    exact (ContinuousLinearMap.opNorm_smul_le _ _).trans
      (by simpa only [Real.norm_eq_abs] using mul_le_mul_of_nonneg_left (hM x) (abs_nonneg s⁻¹))
  · rw [integral_div, hg0, zero_div]
  · simp only [div_pow]
    rw [integral_div, hs2, div_self hpos.ne']
  · intro u
    have heq : (fun x => ⟪u, x⟫ * (g x / s)) = fun x => (⟪u, x⟫ * g x) / s := by
      funext x
      ring
    rw [heq, integral_div, hgorth u, zero_div]
open FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
section MeasurableSpace
variable {A : Type*}
variable [MeasurableSpace A]
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.integral_sq_eq_norm_sq
    (μ : Measure A) {g : A → ℝ} (hg : MemLp g 2 μ) :
    (∫ x, g x ^ 2 ∂μ) = (eLpNorm g 2 μ).toReal ^ 2 := by
  let G : Lp ℝ 2 μ := hg.toLp g
  have hG : G =ᵐ[μ] g := hg.coeFn_toLp
  calc
    (∫ x, g x ^ 2 ∂μ) = ∫ x, (G x) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hG] with x hx
      rw [hx]
    _ = ∫ x, ⟪G x, G x⟫ ∂μ := by
      congr 1
      funext x
      simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    _ = ⟪G, G⟫ := (MeasureTheory.L2.inner_def G G).symm
    _ = ‖G‖ ^ 2 := real_inner_self_eq_norm_sq G
    _ = (eLpNorm g 2 μ).toReal ^ 2 := by rw [Lp.norm_toLp]
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.norm_error_le (μ : Measure A)
    {f g : A → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : eLpNorm (f - g) 2 μ ≤ ENNReal.ofReal ε) :
    (eLpNorm (f - g) 2 μ).toReal ≤ ε ∧
      (eLpNorm g 2 μ).toReal ≤ (eLpNorm f 2 μ).toReal + ε := by
  have hfg : MemLp (f - g) 2 μ := hf.sub hg
  have herr : (eLpNorm (f - g) 2 μ).toReal ≤ ε := by
    simpa only [ENNReal.toReal_ofReal hε] using
      (ENNReal.toReal_le_toReal hfg.eLpNorm_ne_top ENNReal.ofReal_ne_top).2 happrox
  refine ⟨herr, ?_⟩
  have htri := eLpNorm_sub_le hf.aestronglyMeasurable hfg.aestronglyMeasurable one_le_two
  have heq : f - (f - g) = g := by funext x; simp
  rw [heq] at htri
  have ht := (ENNReal.toReal_le_toReal hg.eLpNorm_ne_top
    (ENNReal.add_ne_top.mpr ⟨hf.eLpNorm_ne_top, hfg.eLpNorm_ne_top⟩)).2 htri
  rw [ENNReal.toReal_add hf.eLpNorm_ne_top hfg.eLpNorm_ne_top] at ht
  linarith
end MeasurableSpace
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.coeffs_const_mul {n d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (c : ℝ) (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ (fun x => c * g x) d) =
      c • coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ g d) := by
  rw [taylorTensor_const_mul_408915f]
  ext J
  simp [coordTensor_apply]
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.coeffs_add {n d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ (fun x => f x + g x) d) =
      coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ f d) +
        coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ g d) := by
  rw [taylorTensor_add_408915f μ hexp hf hg]
  ext J
  simp [coordTensor_apply]
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.smooth_homogeneous_bound {n d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (B : ℝ)
    (hunit : ∀ q : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 2 q →
      (∃ M : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ q) x‖ ≤ M) → MemLp q 2 μ →
      (∫ x, q x ∂μ) = 0 → (∫ x, q x ^ 2 ∂μ) = 1 →
      (∀ u, ∫ x, ⟪u, x⟫ * q x ∂μ = 0) →
      ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ q d)‖ ^ 2 ≤ B)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContDiff ℝ ∞ g)
    (hM : ∃ M : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ M)
    (hg2 : MemLp g 2 μ) (hg0 : ∫ x, g x ∂μ = 0)
    (hgorth : ∀ u, ∫ x, ⟪u, x⟫ * g x ∂μ = 0) :
    ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ g d)‖ ^ 2 ≤
      B * (eLpNorm g 2 μ).toReal ^ 2 := by
  let s : ℝ := (eLpNorm g 2 μ).toReal
  have hsnonneg : 0 ≤ s := ENNReal.toReal_nonneg
  by_cases hs0 : s = 0
  · obtain ⟨C, hC⟩ := exists_norm_coordTensor_taylorTensor_le_408915f μ hexp
      (EuclideanSpace.basisFun (Fin n) ℝ) d
    have hs0' : (eLpNorm g 2 μ).toReal = 0 := hs0
    have hnormle : ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ g d)‖ ≤ 0 := by
      simpa only [hs0', mul_zero] using hC g hg2
    have hnzero := le_antisymm hnormle (norm_nonneg _)
    simp only [hnzero, hs0', zero_pow (by norm_num : 2 ≠ 0), mul_zero, le_refl]
  · have hs : 0 < s := lt_of_le_of_ne hsnonneg (Ne.symm hs0)
    have hpos : 0 < ∫ x, g x ^ 2 ∂μ := by
      rw [integral_sq_eq_norm_sq μ hg2]
      exact sq_pos_of_pos hs
    have hsqrt : Real.sqrt (∫ x, g x ^ 2 ∂μ) = s := by
      rw [integral_sq_eq_norm_sq μ hg2]
      exact Real.sqrt_sq hsnonneg
    have hnorm := normalize_smooth_test μ hg hM hg2 hg0 hgorth hpos
    dsimp only at hnorm
    rw [hsqrt] at hnorm
    obtain ⟨hq, hqM, hq2, hq0, hq1, hqorth⟩ := hnorm
    have hqbound := hunit (fun x => g x / s)
      (hq.of_le (WithTop.coe_le_coe.mpr le_top)) hqM hq2 hq0 hq1 hqorth
    have hnormscale :
        ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
            (taylorTensor μ (fun x => g x / s) d)‖ =
          ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ g d)‖ / s := by
      have heq : (fun x => g x / s) = fun x => s⁻¹ * g x := by funext x; ring
      rw [heq, coeffs_const_mul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)]
      ring
    rw [hnormscale, div_pow] at hqbound
    exact (div_le_iff₀ (sq_pos_of_pos hs)).1 hqbound
namespace FunctionalInequalities.KLS.LogConcave.Suspension
end FunctionalInequalities.KLS.LogConcave.Suspension
open FunctionalInequalities.KLS.LogConcave.Suspension in
/-- Exact source affine-orthogonal density extension endpoint: the normalized smooth estimate extends to the full affine-
orthogonal L2 subspace by actual smooth bounded-Hessian density and actual Taylor continuity. -/
theorem solution {d : ℕ} {b : ℝ} (hb : 0 ≤ b) {n : ℕ}
    (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ} (hV : FunctionalInequalities.KLS.RegularPotential V a b')
    (hiso : FunctionalInequalities.KLS.Isotropic hV.law)
    (h113 : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 2 g →
      (∃ M : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ M) → MemLp g 2 (hV.law : Measure _) →
      ∫ x, g x ∂(hV.law : Measure _) = 0 →
      ∫ x, g x ^ 2 ∂(hV.law : Measure _) = 1 →
      (∀ u, ∫ x, ⟪u, x⟫ * g x ∂(hV.law : Measure _) = 0) →
      ‖FunctionalInequalities.Analysis.Tensor.coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (FunctionalInequalities.Analysis.BakryEmery.taylorTensor (hV.law : Measure _) g d)‖ ^ 2 ≤
        b / (d.factorial : ℝ) ^ 2)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 (hV.law : Measure _))
    (hf0 : ∫ x, f x ∂(hV.law : Measure _) = 0)
    (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂(hV.law : Measure _) = 0) :
    ‖FunctionalInequalities.Analysis.Tensor.coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (FunctionalInequalities.Analysis.BakryEmery.taylorTensor (hV.law : Measure _) f d)‖ ^ 2 ≤
      b / (d.factorial : ℝ) ^ 2 * (eLpNorm f 2 (hV.law : Measure _)).toReal ^ 2 := by
  let μ : Measure (EuclideanSpace ℝ (Fin n)) := hV.law
  let B : ℝ := b / (d.factorial : ℝ) ^ 2
  let A : (EuclideanSpace ℝ (Fin n) → ℝ) → FunctionalInequalities.Analysis.Tensor.Coord n d :=
    fun g => FunctionalInequalities.Analysis.Tensor.coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ g d)
  have hB : 0 ≤ B := div_nonneg hb (sq_nonneg _)
  have hroot : 0 ≤ Real.sqrt B := Real.sqrt_nonneg _
  have hrootsq : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB
  have hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ :=
    hV.integrable_exp_mul_norm_408915f
  obtain ⟨C, hC⟩ := FunctionalInequalities.Analysis.BakryEmery.exists_norm_coordTensor_taylorTensor_le_408915f μ hexp
    (EuclideanSpace.basisFun (Fin n) ℝ) d
  let C0 : ℝ := max C 0
  have hC0 : 0 ≤ C0 := le_max_right C 0
  have hcont (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : MemLp g 2 μ) :
      ‖A g‖ ≤ C0 * (eLpNorm g 2 μ).toReal :=
    (hC g hg).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) ENNReal.toReal_nonneg)
  have hnorm : ‖A f‖ ≤ Real.sqrt B * (eLpNorm f 2 μ).toReal := by
    apply le_of_forall_pos_le_add
    intro η hη
    let K : ℝ := C0 + Real.sqrt B
    have hK : 0 ≤ K := add_nonneg hC0 hroot
    let ε : ℝ := η / (K + 1)
    have hden : 0 < K + 1 := by linarith
    have hε : 0 < ε := div_pos hη hden
    have hεeq : ε * (K + 1) = η := (div_mul_cancel₀ _ hden.ne')
    have hKε : K * ε ≤ η := by nlinarith [hε.le]
    obtain ⟨g, hgSmooth, hgM, hg2, hg0, hgorth, happrox⟩ :=
      exists_smooth_bounded_hessian_approx μ
        hiso.memLp_two hiso.mean_zero hiso.integral_inner_mul_inner hf hf0 hfx hε
    obtain ⟨herr, hgnorm⟩ := norm_error_le μ hf hg2 hε.le happrox
    have hgBound : ‖A g‖ ^ 2 ≤ B * (eLpNorm g 2 μ).toReal ^ 2 :=
      smooth_homogeneous_bound μ hexp B h113 hgSmooth hgM hg2 hg0 hgorth
    have hgBoundNorm : ‖A g‖ ≤ Real.sqrt B * (eLpNorm g 2 μ).toReal := by
      have hrnonneg : 0 ≤ Real.sqrt B * (eLpNorm g 2 μ).toReal :=
        mul_nonneg hroot ENNReal.toReal_nonneg
      have hsq : (Real.sqrt B * (eLpNorm g 2 μ).toReal) ^ 2 =
          B * (eLpNorm g 2 μ).toReal ^ 2 := by rw [mul_pow, hrootsq]
      nlinarith [sq_nonneg (‖A g‖ - Real.sqrt B * (eLpNorm g 2 μ).toReal), norm_nonneg (A g)]
    have hfg2 : MemLp (f - g) 2 μ := hf.sub hg2
    have heq : (fun x => (f - g) x + g x) = f := by funext x; simp
    have hadd : A f = A (f - g) + A g := by
      have ht := coeffs_add μ hexp hfg2 hg2 (d := d)
      rw [heq] at ht
      exact ht
    calc
      ‖A f‖ = ‖A (f - g) + A g‖ := congrArg norm hadd
      _ ≤ ‖A (f - g)‖ + ‖A g‖ := norm_add_le _ _
      _ ≤ C0 * (eLpNorm (f - g) 2 μ).toReal + Real.sqrt B * (eLpNorm g 2 μ).toReal :=
        add_le_add (hcont (f - g) hfg2) hgBoundNorm
      _ ≤ C0 * ε + Real.sqrt B * ((eLpNorm f 2 μ).toReal + ε) :=
        add_le_add (mul_le_mul_of_nonneg_left herr hC0) (mul_le_mul_of_nonneg_left hgnorm hroot)
      _ = Real.sqrt B * (eLpNorm f 2 μ).toReal + K * ε := by dsimp [K]; ring
      _ ≤ Real.sqrt B * (eLpNorm f 2 μ).toReal + η := add_le_add le_rfl hKε
  change ‖A f‖ ^ 2 ≤ B * (eLpNorm f 2 μ).toReal ^ 2
  have hsq : (Real.sqrt B * (eLpNorm f 2 μ).toReal) ^ 2 =
      B * (eLpNorm f 2 μ).toReal ^ 2 := by rw [mul_pow, hrootsq]
  nlinarith [norm_nonneg (A f), mul_nonneg hroot (ENNReal.toReal_nonneg (a := eLpNorm f 2 μ))]
