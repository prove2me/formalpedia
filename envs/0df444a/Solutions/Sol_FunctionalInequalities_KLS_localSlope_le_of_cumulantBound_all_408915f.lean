-- Prove2me | solution 1 for FunctionalInequalities.KLS.localSlope_le_of_cumulantBound_all_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T18:21:08.494179+00:00
-- url     : https://prove2.me/submissions/2b01bd03-58e8-47e0-9a53-1c9f359f26c7

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_LocalDerivatives
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Log
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
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_TemperateGrowth
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
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_PoissonIterate_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_PoissonIterate_Criterion
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_PoissonIterate_Permutation
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_PoissonIterate_Taylor
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_PoissonIterate_TaylorRecursion
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
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Growth
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Hessian
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Posterior
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Regular
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_RegularApproximation
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Hessian
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Markov
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_OperatorCore
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Isotropic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Regular_Affine
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Regular_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Regular_Isometry
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Translation
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Closure
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Multiplier
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Statement
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_AffineDecomposition
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_BoundedMultiplier
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
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_IntrinsicTranslation
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_Laplace
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_QuadraticTilt
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
import Mathlib
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
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
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
import Mathlib.Analysis.InnerProductSpace.Spectrum
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
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.MulExpNegMulSq
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
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
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Order.Filter.ENNReal
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Moments.Tilted
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_convexOn_of_hessian_ge_408915f
import Theorems.Thm_FunctionalInequalities_Energy_SmoothGradient_Test_exists_ambient_extension_408915f
import Theorems.Thm_FunctionalInequalities_KLS_Isotropic_map_linearIsometryEquiv_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_isBorellDensity_of_eq_tilted_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_localSlope_le_of_regular_isotropic_bound_408915f
import Theorems.Thm_FunctionalInequalities_KLS_RegularPotential_poincare_le_of_cumulantBound_408915f
import Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_holds_iff_localSlope_408915f
import Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_holds_map_linearIsometryEquiv_iff_408915f
import Theorems.Thm_FunctionalInequalities_Probability_affineSupport_intrinsicMeasure_408915f

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
universe u v
section TiltTransport
section MeasurableSpace
variable {A B : Type*}
variable [MeasurableSpace A] [MeasurableSpace B]
/-- Pushing a density through a measurable equivalence: the new density is the old one composed with
the inverse. -/
theorem FunctionalInequalities.Probability.map_withDensity_measurableEquiv
    (e : A ≃ᵐ B) (μ : Measure A) (w : A → ENNReal) (hw : Measurable w) :
    (μ.withDensity w).map e = (μ.map e).withDensity (fun y => w (e.symm y)) := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [lintegral_map hφ e.measurable,
    lintegral_withDensity_eq_lintegral_mul μ hw (show Measurable (fun x => φ (e x)) from hφ.comp e.measurable),
    lintegral_withDensity_eq_lintegral_mul (μ.map e) (show Measurable (fun y => w (e.symm y)) from hw.comp e.symm.measurable) hφ]
  simp only [Pi.mul_apply]
  rw [lintegral_map (show Measurable (fun y => w (e.symm y) * φ y) from (hw.comp e.symm.measurable).mul hφ) e.measurable]
  simp only [e.symm_apply_apply]
/-- The tilted measure transported through a measurable equivalence is the tilt of the image measure by
the composed weight. -/
theorem FunctionalInequalities.Probability.map_tilted_measurableEquiv
    (e : A ≃ᵐ B) (μ : Measure A) (f : A → ℝ) (hf : Measurable f) :
    (μ.tilted f).map e = (μ.map e).tilted (fun y => f (e.symm y)) := by
  have hZ : (∫ y, Real.exp (f (e.symm y)) ∂(μ.map e)) = ∫ x, Real.exp (f x) ∂μ := by
    simpa only [Function.comp_def, e.symm_apply_apply] using
      integral_map e.measurable.aemeasurable
        ((hf.comp e.symm.measurable).exp.aestronglyMeasurable)
  unfold Measure.tilted
  rw [Probability.map_withDensity_measurableEquiv e μ _ (hf.exp.div_const _).ennreal_ofReal, hZ]
end MeasurableSpace
end TiltTransport
end
end
end

section
noncomputable section
open MeasureTheory Set Topology
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]
omit [CompleteSpace E] in
/-- Log-concavity is retained on the direction of the affine support, even for singular
ambient laws and a zero-dimensional carrier. -/
theorem FunctionalInequalities.KLS.LogConcave.intrinsicMeasure {μ : ProbabilityMeasure E} (hμ : LogConcave μ) :
    LogConcave (Probability.intrinsicMeasure μ) :=
  hμ.of_affineIsometry_map (Probability.intrinsicMeasure μ) (Probability.reconstruct μ)
    (Probability.measurePreserving_reconstruct μ).map_eq
omit [CompleteSpace E] in
/-- The intrinsic support has nonempty interior. This includes the singleton topology in
dimension zero and does not assert that the boundary has zero probability mass. -/
theorem FunctionalInequalities.KLS.LogConcave.interior_intrinsic_support_nonempty {μ : ProbabilityMeasure E}
    (hμ : LogConcave μ) :
    (interior (Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction).support).Nonempty := by
  apply hμ.intrinsicMeasure.convex_support.interior_nonempty_iff_affineSpan_eq_top.mpr
  exact Probability.affineSupport_intrinsicMeasure_408915f μ
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Metric Set Topology
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
section Intrinsic
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [FiniteDimensional ℝ F]
omit [CompleteSpace F] in
/-- Every compact-set log-concave probability law is absolutely continuous in its own affine
support coordinates. Singular ambient measures and the zero-dimensional support are included. -/
theorem FunctionalInequalities.KLS.LogConcave.intrinsic_absolutelyContinuous {μ : ProbabilityMeasure F}
    (hμ : LogConcave μ) (m : Measure (Probability.affineSupport μ).direction)
    [m.IsAddHaarMeasure] :
    (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ≪ m :=
  hμ.intrinsicMeasure.absolutelyContinuous_of_interior_support_nonempty m
    hμ.interior_intrinsic_support_nonempty
end Intrinsic
end
end
end
end
end

section
noncomputable section
open MeasureTheory Set
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
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : ProbabilityMeasure V}
/-- A law `ν = volume.tilted (-W)` with continuous convex `W` is log-concave: its density
`e^{-W} / ∫ e^{-W}` is a log-concave Borell density (`IsBorellDensity.compactLogConcave`). -/
theorem FunctionalInequalities.KLS.LogConcave.logConcave_of_eq_tilted {W : V → ℝ}
    (hνW : (ν : Measure V) = (volume : Measure V).tilted (-W)) (hW : Continuous W)
    (hconv : ConvexOn ℝ Set.univ W) : LogConcave ν := by
  exact
    IsBorellDensity.compactLogConcave
      (isBorellDensity_of_eq_tilted_408915f hνW hW hconv)
end
end
end
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
section
namespace FunctionalInequalities.Poincare.LocalSlope
end FunctionalInequalities.Poincare.LocalSlope
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.LocalSlope
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
omit [InnerProductSpace ℝ E] [CompleteSpace E] [BorelSpace E]
  [SecondCountableTopology E] [FiniteDimensional ℝ E] in
/-- All tests on a zero-dimensional coordinate space have zero variance. -/
theorem FunctionalInequalities.Poincare.LocalSlope.holds_zero_of_subsingleton [Subsingleton E] (ν : ProbabilityMeasure E) :
    Holds ν 0 := by
  intro f _
  have hf : f = fun _ ↦ f 0 := funext fun y ↦ congrArg f (Subsingleton.elim y 0)
  rw [hf]
  simp [evariance]
omit [CompleteSpace E] in
/-- The literature optimum includes the zero-dimensional case with value zero. -/
theorem FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant_eq_zero_of_subsingleton [Subsingleton E] (μ : ProbabilityMeasure E) :
    Poincare.LocalSlope.Intrinsic.constant μ = 0 := by
  apply le_antisymm ?_ bot_le
  exact iInf_le_of_le ⟨0, Poincare.LocalSlope.holds_zero_of_subsingleton (Probability.intrinsicMeasure μ)⟩
    (by simp)
end
end
end
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
section
namespace FunctionalInequalities.Poincare.SmoothTest
end FunctionalInequalities.Poincare.SmoothTest
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.SmoothTest
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
  [MeasurableSpace E]
/-- Source: local order consequence of `constant` and Mathlib's `iInf_le_of_le`.
Every finite valid constant bounds the optimal constant from above. -/
theorem FunctionalInequalities.Poincare.SmoothTest.constant_le {μ : Measure E} {C : NNReal}
    (hC : Holds μ (C : ℝ)) :
    constant μ ≤ (C : ENNReal) := by
  exact iInf_le_of_le ⟨C, hC⟩ le_rfl
/-- Source: local order consequence of `constant` and Mathlib's `le_iInf`.
A lower bound for every finite valid constant bounds the optimal constant from below. -/
theorem FunctionalInequalities.Poincare.SmoothTest.le_constant {μ : Measure E} {L : ENNReal}
    (hL : ∀ C : NNReal, Holds μ (C : ℝ) → L ≤ (C : ENNReal)) :
    L ≤ constant μ := by
  refine le_iInf fun C ↦ ?_
  exact hL C.1 C.2
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section
namespace FunctionalInequalities.Energy.SmoothGradient
end FunctionalInequalities.Energy.SmoothGradient
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.SmoothGradient
open Euclidean
universe u
private theorem FunctionalInequalities.Energy.SmoothGradient.pullbackTest_energy_le
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y] [MeasurableSpace Y]
    {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y} (f : Test ν)
    (φ : X → Y) (hφ : ContDiff ℝ ∞ φ) (hlip : LipschitzWith 1 φ)
    (hmp : MeasurePreserving φ (μ : Measure X) (ν : Measure Y)) :
    (FunctionalInequalities.Energy.SmoothGradient.pullbackTest f φ hφ hlip hmp).energy ≤ f.energy := by
  apply NNReal.coe_le_coe.mp
  calc
    _ ≤ ∫ x, ‖gradient f (φ x)‖ ^ 2 ∂(μ : Measure X) := by
      apply integral_mono (FunctionalInequalities.Energy.SmoothGradient.pullbackTest f φ hφ hlip hmp).gradient_sq_integrable
        (hmp.integrable_comp_of_integrable f.gradient_sq_integrable)
      intro x
      exact pow_le_pow_left₀ (norm_nonneg _) (FunctionalInequalities.Energy.SmoothGradient.norm_gradient_comp_le f.contDiff hφ hlip x) 2
    _ = _ := by
      have h := integral_map hmp.measurable.aemeasurable
        (hmp.map_eq.symm ▸ f.gradient_sq_integrable.aestronglyMeasurable)
      simpa only [hmp.map_eq, Test.coe_energy] using h.symm
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  (μ : ProbabilityMeasure E)
section
namespace FunctionalInequalities.Energy.SmoothGradient.Test
end FunctionalInequalities.Energy.SmoothGradient.Test
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.SmoothGradient FunctionalInequalities.Energy.SmoothGradient.Test
/-- Restriction has the expected `L²` realization and does not increase raw energy.
Source: the tangential-gradient projection argument in the local Blueprint comparison. -/
theorem FunctionalInequalities.Energy.SmoothGradient.Test.exists_intrinsic_restriction (f : Energy.SmoothGradient.Test μ) :
    ∃ g : Energy.SmoothGradient.Test (Probability.intrinsicMeasure μ),
      (∀ v, g v = f (Probability.reconstruct μ v)) ∧
      g.toL2 = toIntrinsicL2 μ f.toL2 ∧ g.energy ≤ f.energy := by
  let φ := Probability.reconstruct μ
  have hφ : ContDiff ℝ ∞ φ := φ.toContinuousAffineMap.contDiff
  let g := FunctionalInequalities.Energy.SmoothGradient.pullbackTest f φ hφ φ.isometry.lipschitz
    (Probability.measurePreserving_reconstruct μ)
  exact ⟨g, fun _ ↦ rfl, rfl,
    pullbackTest_energy_le f φ hφ φ.isometry.lipschitz
      (Probability.measurePreserving_reconstruct μ)⟩
end
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
section
namespace FunctionalInequalities.Poincare.SmoothTest
end FunctionalInequalities.Poincare.SmoothTest
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.SmoothTest
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
/-- Step 6: equality of the infima of valid finite constants on this same coordinate space.
The subtype infimum is the existing Poincare.LocalSlope.Holds definition, without a second intrinsic map. -/
theorem FunctionalInequalities.Poincare.SmoothTest.constant_eq_localSlope_infimum (ν : ProbabilityMeasure E) (m : Measure E)
    [Measure.IsAddHaarMeasure m] (hν : (ν : Measure E) ≪ m) :
    constant (ν : Measure E) =
      ⨅ C : {C : NNReal // Poincare.LocalSlope.Holds ν C}, (C.1 : ENNReal) := by
  apply le_antisymm
  · refine le_iInf fun C => ?_
    exact constant_le ((holds_iff_localSlope_408915f ν m hν C.1).mpr C.2)
  · apply le_constant
    intro C hC
    exact iInf_le_of_le ⟨C, (holds_iff_localSlope_408915f ν m hν C).mp hC⟩ le_rfl
/-- Smooth inequalities transport between the ambient law and its intrinsic law without
absolute continuity. Restriction decreases energy, while normal-constant extension preserves it. -/
private theorem FunctionalInequalities.Poincare.SmoothTest.holds_iff_intrinsicMeasure (μ : ProbabilityMeasure E) (C : NNReal) :
    Holds (μ : Measure E) (C : ℝ) ↔
      Holds (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) (C : ℝ) := by
  let ν := Probability.intrinsicMeasure μ
  have hvar (f : Energy.SmoothGradient.Test μ)
      (g : Energy.SmoothGradient.Test ν)
      (heq : ∀ v, g v = f (Probability.reconstruct μ v)) :
      ProbabilityTheory.variance g.toFun (ν : Measure (Probability.affineSupport μ).direction) =
        ProbabilityTheory.variance f.toFun (μ : Measure E) := by
    calc
      _ = ProbabilityTheory.variance (fun v => f (Probability.reconstruct μ v))
          (ν : Measure (Probability.affineSupport μ).direction) :=
        congrArg (fun k => ProbabilityTheory.variance k (ν : Measure _)) (funext heq)
      _ = _ := (Probability.measurePreserving_reconstruct μ).variance_fun_comp
        f.contDiff.continuous.aemeasurable
  constructor
  · intro h
    refine ⟨inferInstance, C.2, ?_⟩
    intro g hg
    let gt : Energy.SmoothGradient.Test ν :=
      ⟨g, hg.smooth', hg.memLp_two, hg.energy_integrable⟩
    obtain ⟨f, heq, _, henergy⟩ :=
      Energy.SmoothGradient.Test.exists_ambient_extension_408915f μ gt
    have he : energy (μ : Measure E) f.toFun = energy (ν : Measure _) gt.toFun :=
      congrArg (fun c : NNReal => (c : ℝ)) henergy
    change ProbabilityTheory.variance gt.toFun (ν : Measure _) ≤ C * energy (ν : Measure _) gt.toFun
    rw [hvar f gt (fun v => (heq v).symm), ← he]
    exact h.variance_le ⟨f.contDiff, f.memLp_two, f.gradient_sq_integrable⟩
  · intro h
    refine ⟨inferInstance, C.2, ?_⟩
    intro f hf
    let ft : Energy.SmoothGradient.Test μ :=
      ⟨f, hf.smooth', hf.memLp_two, hf.energy_integrable⟩
    obtain ⟨g, heq, _, henergy⟩ :=
      Energy.SmoothGradient.Test.exists_intrinsic_restriction μ ft
    have he : energy (ν : Measure _) g.toFun ≤ energy (μ : Measure E) ft.toFun :=
      NNReal.coe_le_coe.mpr henergy
    have hb := h.variance_le ⟨g.contDiff, g.memLp_two, g.gradient_sq_integrable⟩
    change ProbabilityTheory.variance ft.toFun (μ : Measure E) ≤ C * energy (μ : Measure E) ft.toFun
    rw [← hvar ft g heq]
    exact hb.trans (mul_le_mul_of_nonneg_left he C.2)
/-- Step 7: the exact ambient / intrinsic / literature chain from the Blueprint theorem.
Use the proved smooth-test restriction and normal-constant extension for the first equality.
The Haar reference lives on the direction of the affine support; zero dimension is included. -/
theorem FunctionalInequalities.Poincare.SmoothTest.constant_eq_intrinsicMeasure_and_localSlope (μ : ProbabilityMeasure E)
    (m : Measure (Probability.affineSupport μ).direction) [Measure.IsAddHaarMeasure m]
    (hμ : (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ≪ m) :
    constant (μ : Measure E) =
        constant (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ∧
      constant (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) =
        Poincare.LocalSlope.Intrinsic.constant μ := by
  constructor
  · apply le_antisymm
    · apply le_constant
      intro C hC
      exact constant_le ((holds_iff_intrinsicMeasure μ C).mpr hC)
    · apply le_constant
      intro C hC
      exact constant_le ((holds_iff_intrinsicMeasure μ C).mp hC)
  · exact constant_eq_localSlope_infimum (Probability.intrinsicMeasure μ) m hμ
end
end
end
end
end

section
noncomputable section
open MeasureTheory
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
/-- The ambient smooth-test, intrinsic smooth-test, and intrinsic literature optima agree
for every log-concave probability law. Absolute continuity is derived, not assumed. -/
theorem FunctionalInequalities.KLS.LogConcave.smoothTest_constant_eq_intrinsic_and_localSlope
    {μ : ProbabilityMeasure E} (hμ : KLS.LogConcave μ) :
    Poincare.SmoothTest.constant (μ : Measure E) =
        Poincare.SmoothTest.constant (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ∧
      Poincare.SmoothTest.constant (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) =
        Poincare.LocalSlope.Intrinsic.constant μ :=
  Poincare.SmoothTest.constant_eq_intrinsicMeasure_and_localSlope μ Measure.addHaar
    (hμ.intrinsic_absolutelyContinuous Measure.addHaar)
/-- The smooth-test optimum equals the literature optimum for every log-concave law. -/
theorem FunctionalInequalities.KLS.LogConcave.smoothTest_constant_eq_localSlope
    {μ : ProbabilityMeasure E} (hμ : KLS.LogConcave μ) :
    Poincare.SmoothTest.constant (μ : Measure E) = Poincare.LocalSlope.Intrinsic.constant μ :=
  (smoothTest_constant_eq_intrinsic_and_localSlope hμ).1.trans
    (smoothTest_constant_eq_intrinsic_and_localSlope hμ).2
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
  FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section
namespace FunctionalInequalities.KLS.RegularPotential
end FunctionalInequalities.KLS.RegularPotential
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.RegularPotential
variable {V : E → ℝ} {a b : ℝ}
theorem FunctionalInequalities.KLS.RegularPotential.logConcave_law (hV : RegularPotential V a b) : LogConcave hV.law := by
  have hW : ContDiff ℝ 2 V := hV.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)
  exact LogConcave.logConcave_of_eq_tilted (ν := hV.law) rfl hW.continuous
    (Analysis.BakryEmery.convexOn_of_hessian_ge_408915f hW hV.pos.le hV.lower)
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
end
end
end
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
section
namespace FunctionalInequalities.Poincare.SmoothTest
end FunctionalInequalities.Poincare.SmoothTest
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.SmoothTest
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
section IsometryTransport
variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
variable (e : E ≃ₗᵢ[ℝ] F) (μ : Measure E) [IsProbabilityMeasure μ]
/-- Source: local consequence of `holds_map_linearIsometryEquiv_iff`, `constant_le`, and
`le_constant`; the extended infimum requires no attaining finite constant. -/
theorem FunctionalInequalities.Poincare.SmoothTest.constant_map_linearIsometryEquiv : constant (μ.map e) = constant μ := by
  apply le_antisymm
  · exact le_constant fun C hC ↦
      constant_le ((holds_map_linearIsometryEquiv_iff_408915f e μ).mpr hC)
  · exact le_constant fun C hC ↦
      constant_le ((holds_map_linearIsometryEquiv_iff_408915f e μ).mp hC)
end IsometryTransport
variable [MeasurableSpace E]
end
end
end
end
end

section
open MeasureTheory
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
universe u v
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
/-- The law of `V ∘ L⁻¹` is the image of the law of `V` under `L`. -/
theorem FunctionalInequalities.KLS.RegularPotential.law_comp_isometry {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b)
    (L : E ≃ₗᵢ[ℝ] F) :
    ((RegularPotential.comp_isometry hV L).law : Measure F) = (hV.law : Measure E).map L := by
  have ht := Probability.map_tilted_measurableEquiv L.toMeasurableEquiv
    (volume : Measure E) (-V) hV.temperate.1.continuous.neg.measurable
  change (volume.tilted (-V)).map L =
    ((volume : Measure E).map L).tilted (-fun y => V (L.symm y)) at ht
  rw [L.measurePreserving.map_eq] at ht
  exact ht.symm
/-- The same identity for probability laws. -/
theorem FunctionalInequalities.KLS.RegularPotential.law_comp_isometry_eq_map {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b)
    (L : E ≃ₗᵢ[ℝ] F) :
    (RegularPotential.comp_isometry hV L).law = Probability.mapLinearIsometryEquiv hV.law L := by
  apply ProbabilityMeasure.toMeasure_injective
  exact RegularPotential.law_comp_isometry hV L
/-- Isotropy is preserved. -/
theorem FunctionalInequalities.KLS.RegularPotential.isotropic_comp_isometry {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b)
    (hiso : KLS.Isotropic hV.law) (L : E ≃ₗᵢ[ℝ] F) :
    KLS.Isotropic (RegularPotential.comp_isometry hV L).law := by
  rw [RegularPotential.law_comp_isometry_eq_map]
  exact hiso.map_linearIsometryEquiv_408915f L
/-- The smooth-test Poincaré constant is preserved. -/
theorem FunctionalInequalities.KLS.RegularPotential.smoothTest_constant_comp_isometry {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b)
    (L : E ≃ₗᵢ[ℝ] F) :
    Poincare.SmoothTest.constant ((RegularPotential.comp_isometry hV L).law : Measure F) =
      Poincare.SmoothTest.constant (hV.law : Measure E) := by
  rw [RegularPotential.law_comp_isometry]
  exact Poincare.SmoothTest.constant_map_linearIsometryEquiv L (hV.law : Measure E)
/-- The literature Poincaré constant is preserved. -/
theorem FunctionalInequalities.KLS.RegularPotential.localSlope_constant_comp_isometry {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b)
    (L : E ≃ₗᵢ[ℝ] F) :
    Poincare.LocalSlope.Intrinsic.constant (RegularPotential.comp_isometry hV L).law =
      Poincare.LocalSlope.Intrinsic.constant hV.law := by
  rw [← (RegularPotential.comp_isometry hV L).logConcave_law.smoothTest_constant_eq_localSlope,
    ← hV.logConcave_law.smoothTest_constant_eq_localSlope]
  exact RegularPotential.smoothTest_constant_comp_isometry hV L
omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- Standard orthonormal coordinates give a regular potential on `ℝⁿ`, `n = dim E`, with the same constants. -/
theorem FunctionalInequalities.KLS.RegularPotential.toEuclidean {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b) :
    KLS.RegularPotential
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        V ((stdOrthonormalBasis ℝ E).repr.symm y)) a b :=
  RegularPotential.comp_isometry hV (stdOrthonormalBasis ℝ E).repr
/-- A Poincaré bound for isotropic regular laws on `ℝⁿ` (`n > 0`) transfers to every isotropic regular law
on a finite-dimensional inner product space (dimension zero has constant `0`). No such bound is asserted. -/
theorem FunctionalInequalities.KLS.RegularPotential.localSlope_le_of_euclidean_bound {K : NNReal}
    (hK : ∀ (n : ℕ), 0 < n → ∀ (V : EuclideanSpace ℝ (Fin n) → ℝ) (a b : ℝ)
      (hV : KLS.RegularPotential V a b), KLS.Isotropic hV.law →
        Poincare.LocalSlope.Intrinsic.constant hV.law ≤ (K : ENNReal))
    {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b)
    (hiso : KLS.Isotropic hV.law) :
    Poincare.LocalSlope.Intrinsic.constant hV.law ≤ (K : ENNReal) := by
  by_cases hdim : Module.finrank ℝ E = 0
  · have : Subsingleton E := Module.finrank_zero_iff.mp hdim
    rw [Poincare.LocalSlope.Intrinsic.constant_eq_zero_of_subsingleton]
    exact bot_le
  rw [← RegularPotential.localSlope_constant_comp_isometry hV (stdOrthonormalBasis ℝ E).repr]
  exact hK (Module.finrank ℝ E) (Nat.pos_of_ne_zero hdim) _ a b (RegularPotential.toEuclidean hV)
    (RegularPotential.isotropic_comp_isometry hV hiso _)
end
end
end

section
open MeasureTheory Filter Topology
noncomputable section
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
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- In positive dimension a regular potential has `b > 0`. -/
private theorem FunctionalInequalities.KLS.LogConcave.regular_upper_pos {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b)
    (hdim : 0 < Module.finrank ℝ E) : 0 < b := by
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hdim
  have hq : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have hab : a * ‖v‖ ^ 2 ≤ b * ‖v‖ ^ 2 := (hV.lower 0 v).trans (hV.upper 0 v)
  have hleft := mul_pos hV.pos hq
  by_contra hb
  have hright : b * ‖v‖ ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hb) (sq_nonneg _)
  linarith
/-- The same reduction from a bound for isotropic regular laws on `ℝⁿ`, `n > 0` (standard coordinates). -/
theorem FunctionalInequalities.KLS.LogConcave.localSlope_le_of_euclidean_regular_isotropic_bound {K : NNReal}
    (hEuclidean : ∀ (n : ℕ), 0 < n →
      ∀ (V : EuclideanSpace ℝ (Fin n) → ℝ) (a b : ℝ) (hV : KLS.RegularPotential V a b),
        0 < b → KLS.Isotropic hV.law →
          Poincare.LocalSlope.Intrinsic.constant hV.law ≤ (K : ENNReal))
    (μ : ProbabilityMeasure E) (hLC : KLS.LogConcave μ) (hiso : KLS.Isotropic μ) :
    Poincare.LocalSlope.Intrinsic.constant μ ≤ (K : ENNReal) := by
  apply localSlope_le_of_regular_isotropic_bound_408915f ?_ μ hLC hiso
  intro V a b hV _hb hViso
  apply RegularPotential.localSlope_le_of_euclidean_bound ?_ hV hViso
  intro n hn U α β hU hUiso
  exact hEuclidean n hn U α β hU (regular_upper_pos hU (by simpa using hn)) hUiso
end
end
end
end
end

open MeasureTheory FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.KLS.LogConcave.Suspension
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
universe u
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities.KLS in
/-- **BKL Theorem 1.1, conditional on Theorem 4.1**: under the universal cumulant bounds
`CumulantBound d ((d!)² K^d)` for all `d ≥ 2` (`K ≥ 1`), every isotropic log-concave law in every
finite-dimensional inner product space has literature Poincaré constant at most `2·C_{3.1}·K`
(the p. 30 reduction for regular laws plus the Section 2 regular approximation). The closed
producer `BKL.Localization.exists_isotropicBound` discharges the hypothesis and proves Theorem 1.1. -/
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K →
      (∀ d : ℕ, 2 ≤ d → FunctionalInequalities.KLS.LogConcave.Suspension.CumulantBound d ((d.factorial : ℝ) ^ 2 * K ^ d)) →
      ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
        [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
        (μ : ProbabilityMeasure E), FunctionalInequalities.KLS.LogConcave μ → FunctionalInequalities.KLS.Isotropic μ →
          FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant μ ≤ ENNReal.ofReal (2 * C * K) := by
  obtain ⟨C, hC, hRegular⟩ := FunctionalInequalities.KLS.RegularPotential.poincare_le_of_cumulantBound_408915f
  refine ⟨C, hC, ?_⟩
  intro K hK hcb E _ _ _ _ _ _ _ μ hLC hiso
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let B : NNReal := ⟨2 * C * K, by positivity⟩
  have hB : (B : ENNReal) = ENNReal.ofReal (2 * C * K) :=
    ENNReal.ofReal_coe_nnreal.symm
  have hEuro : ∀ (n : ℕ), 0 < n →
      ∀ (V : EuclideanSpace ℝ (Fin n) → ℝ) (a b : ℝ) (hV : FunctionalInequalities.KLS.RegularPotential V a b),
        0 < b → FunctionalInequalities.KLS.Isotropic hV.law →
          FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant hV.law ≤ (B : ENNReal) := by
    intro n _hn V a b hV _hb hViso
    rw [hB]
    exact hRegular K hK hcb n V a b hV hViso
  rw [← hB]
  exact FunctionalInequalities.KLS.LogConcave.localSlope_le_of_euclidean_regular_isotropic_bound
    hEuro μ hLC hiso
