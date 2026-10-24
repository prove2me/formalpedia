-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.fderiv_stdTrace_ringInverse_cov_noise_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:14:56.327009+00:00
-- url     : https://prove2.me/submissions/facca6e5-6cbf-40f4-976b-20b540c24f0b

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_LocalDerivatives
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_LipschitzBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Bilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_HilbertSchmidt
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_InverseSqrt
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
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
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_CompactReduction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_CumulantEnergy_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Localization_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Localization_CumulantDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Localization_NoiseBound
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Law
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_FromBorell
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
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Diffusion_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Diffusion_VectorGenerator
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_IntrinsicTranslation
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_Laplace
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactDomain
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactPrior
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_CompactQuadratic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Exponent
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_JointRegularity
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_LogPartition
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
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
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Group.Bounded
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
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
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
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
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
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Order.Filter.ENNReal
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Theorems.Thm_FunctionalInequalities_Analysis_inner_self_pos_of_isPositive_of_isUnit_408915f
import Theorems.Thm_FunctionalInequalities_Covariance_inner_operator_self_pos_of_affineSupport_eq_top_408915f
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_posteriorCovariance_joint_408915f

section
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Posterior
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [SecondCountableTopology Ω]
/-- A measurable statistic bounded on the support is in `L²` of the tilt. -/
theorem FunctionalInequalities.Probability.Posterior.memLp_two_tilted_of_compact (μ : ProbabilityMeasure Ω) (hc : IsCompact (μ : Measure Ω).support)
    {φ f : Ω → ℝ} (hφ : Continuous φ) (hf : Measurable f) {C : ℝ}
    (hb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
    MemLp f 2 ((μ : Measure Ω).tilted φ) := by
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
  apply (integrable_tilted_iff (integrable_exp_of_compact μ hc hφ) (fun x => f x ^ 2)).mpr
  have hd : Integrable (fun x => Real.exp (φ x) * f x ^ 2) (μ : Measure Ω) := by
    apply integrable_exp_mul_of_compact μ hc hφ (hf.pow_const 2) (C := C ^ 2) (sq_nonneg C)
    intro x hx
    rw [norm_pow]
    have hB : 0 ≤ C := (norm_nonneg (f x)).trans (hb x hx)
    exact (sq_le_sq₀ (norm_nonneg _) hB).mpr (hb x hx)
  simpa only [smul_eq_mul] using hd
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Posterior
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
/-- Continuous statistics are in `L²` of every posterior of a compactly supported prior. -/
theorem FunctionalInequalities.Probability.Posterior.memLp_two_tilted_quadraticExponent_of_compact (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E)
    {f : E → ℝ} (hf : Continuous f) :
    MemLp f 2 ((μ : Measure E).tilted (quadraticExponent c Q)) := by
  obtain ⟨C, _hC, hb⟩ := exists_bound_on_support_of_compact μ hc hf
  have hφ : Continuous (quadraticExponent c Q) := by unfold quadraticExponent; fun_prop
  exact memLp_two_tilted_of_compact μ hc hφ hf.measurable hb
end
end
end
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
variable [SecondCountableTopology E] [FiniteDimensional ℝ E]
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
omit [BorelSpace E] in
/-- The barycenter of a probability law with finite second moment lies in its affine support. -/
theorem FunctionalInequalities.Probability.integral_id_mem_affineSupport (μ : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) : (∫ x, x ∂(μ : Measure E)) ∈ affineSupport μ :=
  (affineSupport μ).convex.integral_mem (isClosed_affineSupport μ) (ae_mem_affineSupport μ)
    (hμ.integrable (by norm_num))
end
end
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Covariance
end FunctionalInequalities.Covariance
open FunctionalInequalities FunctionalInequalities.Covariance
open Probability
/-- The ambient covariance operator annihilates the orthogonal complement of the direction of the
affine support. -/
theorem FunctionalInequalities.Covariance.operator_apply_eq_zero_of_mem_orthogonal (μ : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) {w : E} (hw : w ∈ (affineSupport μ).directionᗮ) :
    operator (μ : Measure E) w = 0 := by
  apply ext_inner_right ℝ
  intro y
  rw [operator_inner, inner_zero_left, covarianceBilin_apply hμ]
  have hm : (∫ x, id x ∂(μ : Measure E)) ∈ affineSupport μ := integral_id_mem_affineSupport μ hμ
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_mem_affineSupport μ] with z hz
  have hdir : z - ∫ x, id x ∂(μ : Measure E) ∈ (affineSupport μ).direction :=
    AffineSubspace.vsub_mem_direction hz hm
  show inner ℝ w (z - ∫ x, id x ∂(μ : Measure E)) * inner ℝ y (z - ∫ x, id x ∂(μ : Measure E)) = 0
  rw [Submodule.inner_left_of_mem_orthogonal hdir hw, zero_mul]
end
end
end
end

section
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section FiniteDimensional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
/-- A strictly positive operator (`⟪T v, v⟫ > 0` for `v ≠ 0`) on a finite-dimensional space is a unit. -/
theorem FunctionalInequalities.Analysis.isUnit_of_inner_self_pos (T : E →L[ℝ] E)
    (hpos : ∀ v : E, v ≠ 0 → 0 < ⟪T v, v⟫) : IsUnit T := by
  apply ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.mpr
  apply (LinearMap.isUnit_iff_ker_eq_bot T.toLinearMap).mpr
  apply bot_unique
  intro v hv
  have hv' : T v = 0 := hv
  change v = 0
  by_contra hne
  have hp := hpos v hne
  rw [hv', inner_zero_left] at hp
  exact (lt_irrefl 0) hp
end FiniteDimensional
end
end
end

section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- An injective covariance operator forces full affine support. -/
theorem FunctionalInequalities.Probability.affineSupport_eq_top_of_covariance_injective (μ : ProbabilityMeasure E)
    (h2 : MemLp id 2 (μ : Measure E)) (hinj : Function.Injective (Covariance.operator (μ : Measure E))) :
    Probability.affineSupport μ = ⊤ := by
  have hperp : (Probability.affineSupport μ).directionᗮ = ⊥ := by
    apply bot_unique
    intro w hw
    have h := Covariance.operator_apply_eq_zero_of_mem_orthogonal μ h2 hw
    have hz : w = 0 := hinj (h.trans (map_zero _).symm)
    simpa only [Submodule.mem_bot] using hz
  have hdir : (Probability.affineSupport μ).direction = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hperp
  have hne : (Probability.affineSupport μ : Set E).Nonempty :=
    ⟨Probability.origin μ, (Probability.origin μ).property⟩
  exact (AffineSubspace.direction_eq_top_iff_of_nonempty hne).mp hdir
/-- The covariance operator is self-adjoint. -/
theorem FunctionalInequalities.Covariance.operator_isSelfAdjoint (μ : Measure E) : IsSelfAdjoint (Covariance.operator μ) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change ⟪Covariance.operator μ x, y⟫ = ⟪x, Covariance.operator μ y⟫
  calc
    ⟪Covariance.operator μ x, y⟫ = covarianceBilin μ x y := Covariance.operator_inner μ x y
    _ = covarianceBilin μ y x := covarianceBilin_comm x y
    _ = ⟪Covariance.operator μ y, x⟫ := (Covariance.operator_inner μ y x).symm
    _ = ⟪x, Covariance.operator μ y⟫ := real_inner_comm _ _
end
end

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
universe u v
section TiltAbsoluteContinuity
variable {Ω : Type*} [MeasurableSpace Ω]
/-- A normalized tilt has the same topological support as the base law. -/
theorem FunctionalInequalities.Probability.support_tilted_eq [TopologicalSpace Ω] (μ : Measure Ω) {φ : Ω → ℝ}
    (hi : Integrable (fun x => Real.exp (φ x)) μ) : (μ.tilted φ).support = μ.support :=
  Set.Subset.antisymm (tilted_absolutelyContinuous μ φ).support_mono
    (absolutelyContinuous_tilted hi).support_mono
end TiltAbsoluteContinuity
end
end
end

section
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Posterior
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The posterior has the same support as the prior. -/
theorem FunctionalInequalities.Probability.Posterior.compactPosterior_support (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) :
    (compactPosterior μ hc c Q : Measure E).support = (μ : Measure E).support := by
  exact Probability.support_tilted_eq _ (integrable_exp_of_compact μ hc (by unfold quadraticExponent; fun_prop))
/-- The posterior has the same affine support as the prior. -/
theorem FunctionalInequalities.Probability.Posterior.compactPosterior_affineSupport (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) :
    Probability.affineSupport (compactPosterior μ hc c Q) = Probability.affineSupport μ := by
  unfold Probability.affineSupport
  rw [compactPosterior_support]
/-- The posterior has finite second moment. -/
theorem FunctionalInequalities.Probability.Posterior.compactPosterior_memLp_id_two (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (c : E) (Q : E →L[ℝ] E) :
    MemLp id 2 (compactPosterior μ hc c Q : Measure E) := by
  change MemLp id 2 ((μ : Measure E).tilted (quadraticExponent c Q))
  have hn : MemLp (fun x : E => ‖x‖) 2 ((μ : Measure E).tilted (quadraticExponent c Q)) :=
    memLp_two_tilted_quadraticExponent_of_compact μ hc c Q continuous_norm
  apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
  exact (memLp_two_iff_integrable_sq hn.aestronglyMeasurable).1 hn
/-- For a prior with full affine support every posterior has strictly positive covariance. -/
theorem FunctionalInequalities.Probability.Posterior.compactPosterior_covariance_pos_of_affineSupport_eq_top (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hfull : Probability.affineSupport μ = ⊤)
    (c : E) (Q : E →L[ℝ] E) {v : E} (hv : v ≠ 0) :
    0 < ⟪Covariance.operator (compactPosterior μ hc c Q : Measure E) v, v⟫ := by
  apply Covariance.inner_operator_self_pos_of_affineSupport_eq_top_408915f (compactPosterior μ hc c Q)
    (compactPosterior_memLp_id_two μ hc c Q) ?_ hv
  rw [compactPosterior_affineSupport, hfull]
end
end
end
end
end

section
open MeasureTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- An isotropic law has full affine support. -/
theorem FunctionalInequalities.KLS.Isotropic.affineSupport_eq_top {μ : ProbabilityMeasure E} (hiso : KLS.Isotropic μ) :
    Probability.affineSupport μ = ⊤ := by
  apply Probability.affineSupport_eq_top_of_covariance_injective μ hiso.memLp_two
  rw [hiso.covariance_identity]
  exact fun _ _ h => h
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
@[simp] theorem FunctionalInequalities.Analysis.operatorMatrix_operatorOfMatrix (b : OrthonormalBasis ι ℝ E) (M : Matrix ι ι ℝ) :
    operatorMatrix b (operatorOfMatrix b M) = M := by
  exact (LinearMap.toMatrixOrthonormal b).apply_symm_apply M
@[simp] theorem FunctionalInequalities.Analysis.operatorOfMatrix_operatorMatrix (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) :
    operatorOfMatrix b (operatorMatrix b T) = T := by
  exact congrArg (fun f : E →ₗ[ℝ] E => f.toContinuousLinearMap)
    ((LinearMap.toMatrixOrthonormal b).symm_apply_apply T.toLinearMap)
theorem FunctionalInequalities.Analysis.operatorMatrix_injective (b : OrthonormalBasis ι ℝ E) : Function.Injective (operatorMatrix b) := by
  intro S T h
  have := congrArg (operatorOfMatrix b) h
  simpa only [operatorOfMatrix_operatorMatrix] using this
@[simp] theorem FunctionalInequalities.Analysis.operatorMatrix_mul (b : OrthonormalBasis ι ℝ E) (S T : E →L[ℝ] E) :
    operatorMatrix b (S * T) = operatorMatrix b S * operatorMatrix b T := by
  exact map_mul (LinearMap.toMatrixOrthonormal b) S.toLinearMap T.toLinearMap
@[simp] theorem FunctionalInequalities.Analysis.operatorMatrix_one (b : OrthonormalBasis ι ℝ E) :
    operatorMatrix b (1 : E →L[ℝ] E) = 1 := by
  exact map_one (LinearMap.toMatrixOrthonormal b)
/-- The matrix is positive semidefinite iff the operator is positive (Mathlib `posSemidef_toMatrix_iff`). -/
theorem FunctionalInequalities.Analysis.operatorMatrix_posSemidef_iff (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) :
    (operatorMatrix b T).PosSemidef ↔ T.IsPositive :=
  LinearMap.posSemidef_toMatrix_iff b
theorem FunctionalInequalities.Analysis.operatorOfMatrix_isPositive (b : OrthonormalBasis ι ℝ E) (M : Matrix ι ι ℝ)
    (hM : M.PosSemidef) : (operatorOfMatrix b M).IsPositive := by
  apply (operatorMatrix_posSemidef_iff b _).mp
  simpa only [operatorMatrix_operatorOfMatrix] using hM
/-- The matrix inverse of a unit's matrix is the matrix of `Ring.inverse`. -/
theorem FunctionalInequalities.Analysis.operatorMatrix_ringInverse (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) (hA : IsUnit A) :
    (operatorMatrix b A)⁻¹ = operatorMatrix b (Ring.inverse A) := by
  apply Matrix.inv_eq_right_inv
  rw [← operatorMatrix_mul, Ring.mul_inverse_cancel A hA, operatorMatrix_one]
theorem FunctionalInequalities.Analysis.operatorMatrix_isUnit_iff (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) :
    IsUnit (operatorMatrix b A) ↔ IsUnit A := by
  exact (LinearMap.isUnit_toMatrix_iff b.toBasis).trans
    ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.symm
end OperatorMatrix
end
end
end
end

section
noncomputable section
open scoped MatrixOrder RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
@[simp] theorem FunctionalInequalities.Analysis.operatorMatrix_inverseSqrtIn (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) :
    operatorMatrix b (inverseSqrtIn b A) = CFC.sqrt ((operatorMatrix b A)⁻¹) :=
  operatorMatrix_operatorOfMatrix b _
theorem FunctionalInequalities.Analysis.inverseSqrtIn_isPositive (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) :
    (inverseSqrtIn b A).IsPositive :=
  operatorOfMatrix_isPositive b _ (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _))
theorem FunctionalInequalities.Analysis.inverseSqrtIn_isSelfAdjoint (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) :
    IsSelfAdjoint (inverseSqrtIn b A) := (inverseSqrtIn_isPositive b A).isSelfAdjoint
/-- `σ² = Ring.inverse A` for a positive unit `A`. -/
theorem FunctionalInequalities.Analysis.inverseSqrtIn_mul_self (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (hpos : A.IsPositive) (hunit : IsUnit A) :
    inverseSqrtIn b A * inverseSqrtIn b A = Ring.inverse A := by
  apply operatorMatrix_injective b
  rw [operatorMatrix_mul]
  rw [operatorMatrix_inverseSqrtIn]
  rw [CFC.sqrt_mul_sqrt_self _ ((operatorMatrix_posSemidef_iff b A).mpr hpos).inv.nonneg,
    operatorMatrix_ringInverse b A hunit]
/-- `σ σ* = Ring.inverse A`. -/
theorem FunctionalInequalities.Analysis.inverseSqrtIn_mul_adjoint (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (hpos : A.IsPositive) (hunit : IsUnit A) :
    inverseSqrtIn b A * (inverseSqrtIn b A).adjoint = Ring.inverse A := by
  have hsa : (inverseSqrtIn b A).adjoint = inverseSqrtIn b A :=
    inverseSqrtIn_isSelfAdjoint b A
  rw [hsa]
  exact inverseSqrtIn_mul_self b A hpos hunit
/-- `A σσ* = 1 = σσ* A`. -/
theorem FunctionalInequalities.Analysis.inverseSqrtIn_mul_adjoint_cancel (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (hpos : A.IsPositive) (hunit : IsUnit A) :
    A * (inverseSqrtIn b A * (inverseSqrtIn b A).adjoint) = 1 ∧
      (inverseSqrtIn b A * (inverseSqrtIn b A).adjoint) * A = 1 := by
  rw [inverseSqrtIn_mul_adjoint b A hpos hunit]
  exact ⟨Ring.mul_inverse_cancel A hunit, Ring.inverse_mul_cancel A hunit⟩
theorem FunctionalInequalities.Analysis.inverseSqrtIn_isUnit (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (hpos : A.IsPositive) (hunit : IsUnit A) : IsUnit (inverseSqrtIn b A) := by
  have hp : (operatorMatrix b A).PosDef :=
    ((operatorMatrix_posSemidef_iff b A).mpr hpos).posDef_iff_isUnit.mpr
      ((operatorMatrix_isUnit_iff b A).mpr hunit)
  apply (operatorMatrix_isUnit_iff b _).mp
  rw [operatorMatrix_inverseSqrtIn]
  exact (IsStrictlyPositive.sqrt _ hp.inv.isStrictlyPositive).isUnit
theorem FunctionalInequalities.Analysis.inverseSqrtIn_inner_self_pos (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E)
    (hpos : A.IsPositive) (hunit : IsUnit A) {v : E} (hv : v ≠ 0) :
    0 < ⟪inverseSqrtIn b A v, v⟫ :=
  inner_self_pos_of_isPositive_of_isUnit_408915f b _ (inverseSqrtIn_isPositive b A)
    (inverseSqrtIn_isUnit b A hpos hunit) hv
/-- **Specification of `A^{-1/2}`** for a positive unit `A`: positive, self-adjoint, `σ² = σσ* = Ring.inverse A`,
`A σσ* = σσ* A = 1`. -/
theorem FunctionalInequalities.Analysis.inverseSqrt_spec (A : E →L[ℝ] E) (hpos : A.IsPositive) (hunit : IsUnit A) :
    (inverseSqrt A).IsPositive ∧ IsSelfAdjoint (inverseSqrt A) ∧
      inverseSqrt A * inverseSqrt A = Ring.inverse A ∧
      inverseSqrt A * (inverseSqrt A).adjoint = Ring.inverse A ∧
      A * (inverseSqrt A * (inverseSqrt A).adjoint) = 1 ∧
      (inverseSqrt A * (inverseSqrt A).adjoint) * A = 1 := by
  exact ⟨inverseSqrtIn_isPositive _ A, inverseSqrtIn_isSelfAdjoint _ A,
    inverseSqrtIn_mul_self _ A hpos hunit, inverseSqrtIn_mul_adjoint _ A hpos hunit,
    inverseSqrtIn_mul_adjoint_cancel _ A hpos hunit⟩
end
end
end
end

section
noncomputable section
open MeasureTheory
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
open scoped RealInnerProductSpace ContDiff
open Set
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- For a compactly supported isotropic prior every posterior has strictly positive covariance. -/
theorem FunctionalInequalities.KLS.Isotropic.compactPosterior_covariance_pos (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ)
    (c : E) (Q : E →L[ℝ] E) {v : E} (hv : v ≠ 0) :
    0 < ⟪Covariance.operator (compactPosterior μ hc c Q : Measure E) v, v⟫ :=
  compactPosterior_covariance_pos_of_affineSupport_eq_top μ hc (hiso.affineSupport_eq_top) c Q hv
/-- The posterior covariance is a unit. -/
theorem FunctionalInequalities.KLS.Isotropic.compactPosterior_covariance_isUnit (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) (c : E) (Q : E →L[ℝ] E) :
    IsUnit (Covariance.operator (compactPosterior μ hc c Q : Measure E)) :=
  Analysis.isUnit_of_inner_self_pos _ (fun _ hv => Isotropic.compactPosterior_covariance_pos μ hc hiso c Q hv)
/-- The posterior covariance is a positive operator. -/
theorem FunctionalInequalities.KLS.Isotropic.compactPosterior_covariance_isPositive (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) (c : E) (Q : E →L[ℝ] E) :
    (Covariance.operator (compactPosterior μ hc c Q : Measure E)).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff' _).mpr
  refine ⟨Covariance.operator_isSelfAdjoint _, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  · exact (Isotropic.compactPosterior_covariance_pos μ hc hiso c Q hv).le
/-- **The diffusion coefficient `A^{-1/2}` of (67)**: for a compactly supported isotropic prior and every finite
`(c, Q)` (including `0`, negative `Q`, rank zero), `σ = inverseSqrt (Cov μ_{c,Q})` is self-adjoint, positive,
strictly positive, `σ² = σσ* = Cov⁻¹` and `Cov σσ* = σσ* Cov = 1`. Coefficient algebra only; no regularity,
SDE, Itô or martingale statement. -/
theorem FunctionalInequalities.KLS.Isotropic.compactPosterior_inverseSqrt_spec (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) (c : E) (Q : E →L[ℝ] E) :
    let A := Covariance.operator (compactPosterior μ hc c Q : Measure E)
    let σ := inverseSqrt A
    IsSelfAdjoint σ ∧ σ.IsPositive ∧ (∀ v : E, v ≠ 0 → 0 < ⟪σ v, v⟫) ∧
      σ * σ = Ring.inverse A ∧ σ * σ.adjoint = Ring.inverse A ∧
      A * (σ * σ.adjoint) = 1 ∧ (σ * σ.adjoint) * A = 1 := by
  dsimp only
  let A := Covariance.operator (compactPosterior μ hc c Q : Measure E)
  have hp := Isotropic.compactPosterior_covariance_isPositive μ hc hiso c Q
  have hu := Isotropic.compactPosterior_covariance_isUnit μ hc hiso c Q
  obtain ⟨hpos, hsa, hsquare, hgram, hl, hr⟩ := inverseSqrt_spec A hp hu
  exact ⟨hsa, hpos, fun _ hv => inverseSqrtIn_inner_self_pos _ A hp hu hv,
    hsquare, hgram, hl, hr⟩
variable {ι : Type*} [Fintype ι]
end
end
end
end

section
noncomputable section
open MeasureTheory
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
open scoped RealInnerProductSpace ContDiff
open Set
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section JointCoefficients
/-- **Joint smoothness of the rate** `A⁻¹ = Cov(μ_{c,Q})⁻¹` of (67): isotropy makes the posterior covariance a
unit at every finite `(c, Q)`, and the Banach-algebra inverse is analytic there. -/
theorem FunctionalInequalities.KLS.Isotropic.contDiff_ringInverse_covariance_joint (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) :
    ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) =>
      Ring.inverse (Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E))) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  have hs := (contDiff_posteriorCovariance_joint_408915f μ hc).contDiffAt (x := p)
  obtain ⟨u, hu⟩ := Isotropic.compactPosterior_covariance_isUnit μ hc hiso p.1 p.2
  have hi : ContDiffAt ℝ ∞ Ring.inverse
      (Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E)) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  exact hi.comp p hs
end JointCoefficients
end
end
end
end

section
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.BKL
end FunctionalInequalities.KLS.BKL
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.BKL
section
namespace FunctionalInequalities.KLS.BKL.Localization
end FunctionalInequalities.KLS.BKL.Localization
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.BKL FunctionalInequalities.KLS.BKL.Localization
open scoped ContDiff
variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
/-- Self-adjointness and the square identity of the diffusion coefficient `σ = A(p)^{-1/2}`. -/
theorem FunctionalInequalities.KLS.BKL.Localization.inverseSqrt_cov_props (hiso : KLS.Isotropic μ) (p : Param n) :
    (∀ u v, ⟪inverseSqrt (cov μ hc p) u, v⟫ = ⟪u, inverseSqrt (cov μ hc p) v⟫) ∧
      ∀ v, inverseSqrt (cov μ hc p) (inverseSqrt (cov μ hc p) v) = Ring.inverse (cov μ hc p) v := by
  have hspec := Isotropic.compactPosterior_inverseSqrt_spec μ hc hiso p.1 p.2
  dsimp only at hspec
  obtain ⟨hsa, -, -, hsq, -, -, -⟩ := hspec
  refine ⟨fun u v => ?_, fun v => ?_⟩
  · exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa) u v
  · change (inverseSqrt (cov μ hc p) * inverseSqrt (cov μ hc p)) v = _
    exact congrArg (fun T => T v) hsq
end
end
end
end
end
end

section
noncomputable section
open scoped Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Diffusion
end FunctionalInequalities.Probability.Diffusion
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Diffusion
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
section NormedSpace
variable {W W' : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup W'] [NormedSpace ℝ W']
/-- The derivative of a continuous linear map applied to a differentiable function. -/
theorem FunctionalInequalities.Probability.Diffusion.fderiv_clm_comp_apply_vec (ℓ : W →L[ℝ] W') {G : V → W} {x : V}
    (hG : DifferentiableAt ℝ G x) (v : V) :
    fderiv ℝ (fun y => ℓ (G y)) x v = ℓ (fderiv ℝ G x v) := by
  exact congrArg (fun q : V →L[ℝ] W' => q v)
    (ℓ.hasFDerivAt.comp x hG.hasFDerivAt).fderiv
end NormedSpace
end
end
end
end
end

section
noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Diffusion
end FunctionalInequalities.Probability.Diffusion
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Diffusion
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
section Inverse
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
variable [CompleteSpace R]
/-- **Derivative of the inverse of an operator-valued function**: `D(A⁻¹)(x)[v] = −A⁻¹ (DA[v]) A⁻¹` at a point where
`A x` is a unit. -/
theorem FunctionalInequalities.Probability.Diffusion.fderiv_ringInverse_comp_apply (A : V → R) {x : V} (hA : DifferentiableAt ℝ A x) (hu : IsUnit (A x)) (v : V) :
    fderiv ℝ (fun y => Ring.inverse (A y)) x v =
      -(Ring.inverse (A x) * fderiv ℝ A x v * Ring.inverse (A x)) := by
  have hi :
      HasFDerivAt Ring.inverse
        (-(ContinuousLinearMap.mulLeftRight ℝ R
          (Ring.inverse (A x)) (Ring.inverse (A x)))) (A x) := by
    simpa only [← Ring.inverse_unit, hu.unit_spec] using
      (hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit)
  have hc := (hi.comp x hA.hasFDerivAt).fderiv
  exact congrArg (fun L : V →L[ℝ] R => L v) hc
end Inverse
end
end
end
end
end

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.BKL
end FunctionalInequalities.KLS.BKL
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.BKL
section
namespace FunctionalInequalities.KLS.BKL.Localization
end FunctionalInequalities.KLS.BKL.Localization
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.BKL FunctionalInequalities.KLS.BKL.Localization
private theorem FunctionalInequalities.KLS.BKL.Localization.traceMap_apply {n : ℕ} (M : FunctionalInequalities.KLS.BKL.Localization.Op n) :
    FunctionalInequalities.KLS.BKL.Localization.traceMap M = stdTrace M := by
  simp [FunctionalInequalities.KLS.BKL.Localization.traceMap, FunctionalInequalities.KLS.BKL.Localization.entryMap, stdTrace]
private theorem FunctionalInequalities.KLS.BKL.Localization.sandwich_inner {n : ℕ} (S R H : FunctionalInequalities.KLS.BKL.Localization.Op n)
    (hS : ∀ x y, ⟪S x, y⟫ = ⟪x, S y⟫)
    (hSS : S * S = R) (e : FunctionalInequalities.KLS.BKL.Localization.Vec n) :
    ⟪e, (R * H * R) e⟫ = ⟪S e, (S * H * S) (S e)⟫ := by
  have heq : R * H * R = S * (S * H * S) * S := by
    rw [← hSS]
    simp only [mul_assoc]
  rw [heq]
  change ⟪e, S ((S * H * S) (S e))⟫ = _
  exact (hS e _).symm
variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
private theorem FunctionalInequalities.KLS.BKL.Localization.cov_smooth_two : ContDiff ℝ 2 (cov μ hc) := by
  have h : ContDiff ℝ ∞ (cov μ hc) :=
    contDiff_posteriorCovariance_joint_408915f μ hc
  exact h.of_le (WithTop.coe_le_coe.mpr le_top)
private theorem FunctionalInequalities.KLS.BKL.Localization.inverse_cov_smooth_two (hiso : KLS.Isotropic μ) :
    ContDiff ℝ 2 (fun q : Param n => Ring.inverse (cov μ hc q)) := by
  have h :
      ContDiff ℝ ∞ (fun q : Param n => Ring.inverse (cov μ hc q)) :=
    Isotropic.contDiff_ringInverse_covariance_joint μ hc hiso
  exact h.of_le (WithTop.coe_le_coe.mpr le_top)
namespace FunctionalInequalities.KLS.BKL.Localization
end FunctionalInequalities.KLS.BKL.Localization
open FunctionalInequalities.KLS.BKL.Localization in
set_option maxHeartbeats 1000000 in
/-- The noise derivative of `tr A⁻¹`: `D(tr A⁻¹)[σ e_k] = −Σ_i ⟪σ e_i, H̃_k σ e_i⟫` with
`H̃_k = σ (D_cA[σ e_k]) σ`. -/
theorem solution (hiso : FunctionalInequalities.KLS.Isotropic μ) (p : FunctionalInequalities.KLS.BKL.Localization.Param n) (k : Fin n) :
    fderiv ℝ (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.Analysis.stdTrace (Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q))) p (FunctionalInequalities.KLS.BKL.Localization.noise μ hc p k) =
      -∑ i, ⟪FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.KLS.BKL.Localization.cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ i),
        (FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.KLS.BKL.Localization.cov μ hc p) * fderiv ℝ (FunctionalInequalities.KLS.BKL.Localization.cov μ hc) p (FunctionalInequalities.KLS.BKL.Localization.noise μ hc p k) * FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.KLS.BKL.Localization.cov μ hc p))
          (FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.KLS.BKL.Localization.cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ i))⟫ := by
  have hA : DifferentiableAt ℝ (FunctionalInequalities.KLS.BKL.Localization.cov μ hc) p :=
    (cov_smooth_two μ hc).differentiable (by norm_num) p
  have hR :
      DifferentiableAt ℝ (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q)) p :=
    (inverse_cov_smooth_two μ hc hiso).differentiable (by norm_num) p
  have hu : IsUnit (FunctionalInequalities.KLS.BKL.Localization.cov μ hc p) :=
    FunctionalInequalities.KLS.Isotropic.compactPosterior_covariance_isUnit μ hc hiso p.1 p.2
  have hfun :
      (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.Analysis.stdTrace (Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q))) =
        (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.KLS.BKL.Localization.traceMap (Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q))) :=
    funext fun q => (traceMap_apply (Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q))).symm
  have hSS :
      FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.KLS.BKL.Localization.cov μ hc p) * FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.KLS.BKL.Localization.cov μ hc p) =
        Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc p) := by
    apply ContinuousLinearMap.ext
    intro v
    exact (FunctionalInequalities.KLS.BKL.Localization.inverseSqrt_cov_props μ hc hiso p).2 v
  rw [hfun, FunctionalInequalities.Probability.Diffusion.fderiv_clm_comp_apply_vec FunctionalInequalities.KLS.BKL.Localization.traceMap hR (FunctionalInequalities.KLS.BKL.Localization.noise μ hc p k)]
  rw [FunctionalInequalities.Probability.Diffusion.fderiv_ringInverse_comp_apply
    (FunctionalInequalities.KLS.BKL.Localization.cov μ hc) hA hu (FunctionalInequalities.KLS.BKL.Localization.noise μ hc p k)]
  rw [map_neg, traceMap_apply]
  apply congrArg Neg.neg
  unfold FunctionalInequalities.Analysis.stdTrace
  apply Finset.sum_congr rfl
  intro i _
  exact sandwich_inner
    (FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.KLS.BKL.Localization.cov μ hc p)) (Ring.inverse (FunctionalInequalities.KLS.BKL.Localization.cov μ hc p))
    (fderiv ℝ (FunctionalInequalities.KLS.BKL.Localization.cov μ hc) p (FunctionalInequalities.KLS.BKL.Localization.noise μ hc p k))
    (FunctionalInequalities.KLS.BKL.Localization.inverseSqrt_cov_props μ hc hiso p).1 hSS
    (EuclideanSpace.basisFun (Fin n) ℝ i)
