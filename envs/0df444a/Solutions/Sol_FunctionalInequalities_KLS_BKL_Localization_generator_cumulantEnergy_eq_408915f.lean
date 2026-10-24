-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.generator_cumulantEnergy_eq_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:25:17.509593+00:00
-- url     : https://prove2.me/submissions/1174dcfb-52fa-4ed4-a8c8-478e5f45abc5

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
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_InverseSqrt
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_EnergyForm
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_SlotAction
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
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Localization_CumulantGenerator
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Localization_Energy_Generator
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
import Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_contDiffAt_energyForm_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_inner_self_pos_of_isPositive_of_isUnit_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_inverseSqrt_mul_mul_inverseSqrt_408915f
import Theorems.Thm_FunctionalInequalities_Covariance_inner_operator_self_pos_of_affineSupport_eq_top_408915f
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_contDiff_cumulant_posterior_408915f
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_fderiv_cumulant_posterior_apply_408915f
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_generator_cumulant_posterior_408915f
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_generator_inner_cov_408915f
import Theorems.Thm_FunctionalInequalities_KLS_BKL_cumulantEnergy_eq_energyForm_408915f
import Theorems.Thm_FunctionalInequalities_Probability_Diffusion_diffusionGenerator_comp_of_contDiffAt_408915f
import Theorems.Thm_FunctionalInequalities_Probability_Diffusion_vectorGenerator_clm_comp_408915f
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
/-- For scalar functions the vector generator is the generator. -/
theorem FunctionalInequalities.Probability.Diffusion.diffusionGenerator_eq_vectorGenerator (b : V → V) (σ : V → Fin d → V) (F : V → ℝ) (x : V) :
    diffusionGenerator b σ F x = vectorGenerator b σ F x := by
  simp only [diffusionGenerator, vectorGenerator, smul_eq_mul]
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
section NormedSpace
variable {W₁ W₂ : Type*}
variable [NormedAddCommGroup W₁] [NormedSpace ℝ W₁] [NormedAddCommGroup W₂] [NormedSpace ℝ W₂]
/-- The vector generator of a pair is the pair of vector generators. -/
theorem FunctionalInequalities.Probability.Diffusion.vectorGenerator_prodMk (b : V → V) (σ : V → Fin d → V)
    {G₁ : V → W₁} {G₂ : V → W₂} {x : V} (h₁ : ContDiffAt ℝ 2 G₁ x) (h₂ : ContDiffAt ℝ 2 G₂ x) :
    vectorGenerator b σ (fun y => (G₁ y, G₂ y)) x =
      (vectorGenerator b σ G₁ x, vectorGenerator b σ G₂ x) := by
  apply Prod.ext
  · exact
      (vectorGenerator_clm_comp_408915f b σ
        (ContinuousLinearMap.fst ℝ W₁ W₂) (h₁.prodMk h₂)).symm
  · exact
      (vectorGenerator_clm_comp_408915f b σ
        (ContinuousLinearMap.snd ℝ W₁ W₂) (h₁.prodMk h₂)).symm
/-- The vector generator of a finite family is computed componentwise. -/
theorem FunctionalInequalities.Probability.Diffusion.vectorGenerator_pi {ι : Type*} [Fintype ι] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (b : V → V) (σ : V → Fin d → V) {G : V → ι → W} {x : V}
    (hG : ∀ i, ContDiffAt ℝ 2 (fun y => G y i) x) :
    vectorGenerator b σ G x = fun i => vectorGenerator b σ (fun y => G y i) x := by
  have h : ContDiffAt ℝ 2 G x := contDiffAt_pi.mpr hG
  funext i
  exact
    (vectorGenerator_clm_comp_408915f b σ
      (ContinuousLinearMap.proj i : (ι → W) →L[ℝ] W) h).symm
/-- The derivative of a pair, applied to a vector. -/
theorem FunctionalInequalities.Probability.Diffusion.fderiv_prodMk_apply_vec {G₁ : V → W₁} {G₂ : V → W₂} {x : V}
    (h₁ : DifferentiableAt ℝ G₁ x) (h₂ : DifferentiableAt ℝ G₂ x) (v : V) :
    fderiv ℝ (fun y => (G₁ y, G₂ y)) x v = (fderiv ℝ G₁ x v, fderiv ℝ G₂ x v) := by
  exact congrArg (fun q => q v) (h₁.fderiv_prodMk h₂)
end NormedSpace
/-- The derivative of a finite family, applied to a vector. -/
theorem FunctionalInequalities.Probability.Diffusion.fderiv_pi_apply_vec {ι : Type*} [Fintype ι] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {G : V → ι → W} {x : V} (hG : ∀ i, DifferentiableAt ℝ (fun y => G y i) x) (v : V) :
    fderiv ℝ G x v = fun i => fderiv ℝ (fun y => G y i) x v := by
  rw [fderiv_pi hG]
  funext i
  exact ContinuousLinearMap.pi_apply _ _ _
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
  FunctionalInequalities.Analysis.CoordinateTensor
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
variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
private theorem FunctionalInequalities.KLS.BKL.Localization.covariance_contDiff_two :
    ContDiff ℝ 2 (cov μ hc) :=
  (contDiff_posteriorCovariance_joint_408915f μ hc).of_le
    (WithTop.coe_le_coe.mpr le_top)
private theorem FunctionalInequalities.KLS.BKL.Localization.covariance_vectorGenerator (hiso : KLS.Isotropic μ) (p : Param n) :
    vectorGenerator (drift μ hc) (noise μ hc) (cov μ hc) p = -cov μ hc p := by
  have hA : ContDiffAt ℝ 2 (cov μ hc) p :=
    (covariance_contDiff_two μ hc).contDiffAt
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℝ
  intro y
  let ℓ :
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ :=
    (innerSL ℝ y).comp (ContinuousLinearMap.apply ℝ _ x)
  have hℓ := vectorGenerator_clm_comp_408915f (drift μ hc) (noise μ hc) ℓ hA
  have hs :
      vectorGenerator (drift μ hc) (noise μ hc)
        (fun q => ⟪y, cov μ hc q x⟫) p = -⟪y, cov μ hc p x⟫ := by
    have h := generator_inner_cov_408915f μ hc hiso p x y
    simpa only [generator, diffusionGenerator_eq_vectorGenerator, real_inner_comm]
      using h
  calc
    ⟪y, vectorGenerator (drift μ hc) (noise μ hc) (cov μ hc) p x⟫ =
        ℓ (vectorGenerator (drift μ hc) (noise μ hc) (cov μ hc) p) := rfl
    _ = vectorGenerator (drift μ hc) (noise μ hc)
        (fun q => ℓ (cov μ hc q)) p := hℓ.symm
    _ = -⟪y, cov μ hc p x⟫ := hs
    _ = ⟪y, (-cov μ hc p) x⟫ := by
      change -⟪y, cov μ hc p x⟫ = ⟪y, -(cov μ hc p x)⟫
      exact (inner_neg_right y (cov μ hc p x)).symm
namespace FunctionalInequalities.KLS.BKL.Localization
end FunctionalInequalities.KLS.BKL.Localization
open FunctionalInequalities.KLS.BKL.Localization in
set_option maxHeartbeats 1000000 in
theorem solution (hiso : FunctionalInequalities.KLS.Isotropic μ) {r : ℕ} (hr : 2 ≤ r)
    (u : EuclideanSpace ℝ (Fin n)) (p : FunctionalInequalities.KLS.BKL.Localization.Param n) :
    FunctionalInequalities.KLS.BKL.Localization.generator μ hc
        (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.KLS.BKL.cumulantEnergy (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) r u) p =
      fderiv ℝ (fun q : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × ((Fin r → Fin n) → ℝ) =>
          FunctionalInequalities.Analysis.CoordinateTensor.energyForm q.1 q.2) (1, FunctionalInequalities.KLS.BKL.Localization.energyTensor μ hc p r u)
          (-1, -(((r : ℝ) + 1) • FunctionalInequalities.KLS.BKL.Localization.energyTensor μ hc p r u + FunctionalInequalities.KLS.BKL.Localization.lowerTensor μ hc p r u)) +
        (1 / 2 : ℝ) * ∑ k, fderiv ℝ (fderiv ℝ
          (fun q : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × ((Fin r → Fin n) → ℝ) =>
            FunctionalInequalities.Analysis.CoordinateTensor.energyForm q.1 q.2)) (1, FunctionalInequalities.KLS.BKL.Localization.energyTensor μ hc p r u)
          (FunctionalInequalities.KLS.BKL.Localization.conjugatedNoiseOperator μ hc p k, FunctionalInequalities.KLS.BKL.Localization.noiseTensor μ hc p r u k)
          (FunctionalInequalities.KLS.BKL.Localization.conjugatedNoiseOperator μ hc p k, FunctionalInequalities.KLS.BKL.Localization.noiseTensor μ hc p r u k) := by
  classical
  let P := FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.KLS.BKL.Localization.cov μ hc p)
  let L := FunctionalInequalities.KLS.BKL.Localization.sandwich P
  let dirs (K : Fin r → Fin n) : Fin (r + 1) → EuclideanSpace ℝ (Fin n) :=
    Fin.cons u fun s => P (EuclideanSpace.basisFun (Fin n) ℝ (K s))
  let G₁ : FunctionalInequalities.KLS.BKL.Localization.Param n →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
    fun q => L (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q)
  let G₂ : FunctionalInequalities.KLS.BKL.Localization.Param n → (Fin r → Fin n) → ℝ :=
    fun q K =>
      FunctionalInequalities.Analysis.BakryEmery.cumulant
        (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n)))
        (r + 1) (dirs K)
  let G := fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => (G₁ q, G₂ q)
  let Φ :
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ×
        ((Fin r → Fin n) → ℝ) → ℝ :=
    fun q => FunctionalInequalities.Analysis.CoordinateTensor.energyForm q.1 q.2
  have hpos (q : FunctionalInequalities.KLS.BKL.Localization.Param n) : (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q).IsPositive :=
    FunctionalInequalities.KLS.Isotropic.compactPosterior_covariance_isPositive μ hc hiso q.1 q.2
  have hunit (q : FunctionalInequalities.KLS.BKL.Localization.Param n) : IsUnit (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q) :=
    FunctionalInequalities.KLS.Isotropic.compactPosterior_covariance_isUnit μ hc hiso q.1 q.2
  have hP : IsSelfAdjoint P :=
    (FunctionalInequalities.KLS.Isotropic.compactPosterior_inverseSqrt_spec μ hc hiso p.1 p.2).1
  have hPu : IsUnit P := by
    apply FunctionalInequalities.Analysis.isUnit_of_inner_self_pos P
    intro v hv
    exact
      (FunctionalInequalities.KLS.Isotropic.compactPosterior_inverseSqrt_spec μ hc hiso p.1 p.2).2.2.1 v hv
  have hroot : P * FunctionalInequalities.KLS.BKL.Localization.cov μ hc p * P = 1 :=
    FunctionalInequalities.Analysis.inverseSqrt_mul_mul_inverseSqrt_408915f (FunctionalInequalities.KLS.BKL.Localization.cov μ hc p) (hpos p) (hunit p)
  have hGp : G p = (1, FunctionalInequalities.KLS.BKL.Localization.energyTensor μ hc p r u) := by
    apply Prod.ext
    · exact hroot
    · rfl
  have heq :
      (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n =>
        FunctionalInequalities.KLS.BKL.cumulantEnergy
          (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n)))
          r u) = Φ ∘ G := by
    funext q
    exact FunctionalInequalities.KLS.BKL.cumulantEnergy_eq_energyForm_408915f
      (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n)))
      (hpos q) (hunit q) P hP hPu r u
  have hA : ContDiffAt ℝ 2 (FunctionalInequalities.KLS.BKL.Localization.cov μ hc) p :=
    (covariance_contDiff_two μ hc).contDiffAt
  have hK (K : Fin r → Fin n) :
      ContDiffAt ℝ 2 (fun q => G₂ q K) p :=
    ((FunctionalInequalities.KLS.BKL.Localization.contDiff_cumulant_posterior_408915f μ hc (show 1 ≤ r + 1 by omega) (dirs K)).of_le
      (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  have h₁ : ContDiffAt ℝ 2 G₁ p :=
    L.contDiff.contDiffAt.comp p hA
  have h₂ : ContDiffAt ℝ 2 G₂ p :=
    contDiffAt_pi.mpr hK
  have hG : ContDiffAt ℝ 2 G p := h₁.prodMk h₂
  have hΦ : ContDiffAt ℝ 2 Φ (G p) := by
    rw [hGp]
    exact FunctionalInequalities.Analysis.CoordinateTensor.contDiffAt_energyForm_408915f 1 isUnit_one (FunctionalInequalities.KLS.BKL.Localization.energyTensor μ hc p r u)
  have hv₁ :
      FunctionalInequalities.Probability.Diffusion.vectorGenerator (FunctionalInequalities.KLS.BKL.Localization.drift μ hc) (FunctionalInequalities.KLS.BKL.Localization.noise μ hc) G₁ p = -1 := by
    change FunctionalInequalities.Probability.Diffusion.vectorGenerator (FunctionalInequalities.KLS.BKL.Localization.drift μ hc) (FunctionalInequalities.KLS.BKL.Localization.noise μ hc)
      (fun q => L (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q)) p = -1
    rw [FunctionalInequalities.Probability.Diffusion.vectorGenerator_clm_comp_408915f (FunctionalInequalities.KLS.BKL.Localization.drift μ hc) (FunctionalInequalities.KLS.BKL.Localization.noise μ hc) L hA,
      covariance_vectorGenerator μ hc hiso p, map_neg]
    change -(P * FunctionalInequalities.KLS.BKL.Localization.cov μ hc p * P) = -1
    rw [hroot]
  have hv₂ :
      FunctionalInequalities.Probability.Diffusion.vectorGenerator (FunctionalInequalities.KLS.BKL.Localization.drift μ hc) (FunctionalInequalities.KLS.BKL.Localization.noise μ hc) G₂ p =
        -(((r : ℝ) + 1) • FunctionalInequalities.KLS.BKL.Localization.energyTensor μ hc p r u + FunctionalInequalities.KLS.BKL.Localization.lowerTensor μ hc p r u) := by
    rw [FunctionalInequalities.Probability.Diffusion.vectorGenerator_pi (FunctionalInequalities.KLS.BKL.Localization.drift μ hc) (FunctionalInequalities.KLS.BKL.Localization.noise μ hc) hK]
    funext K
    change
      FunctionalInequalities.Probability.Diffusion.vectorGenerator (FunctionalInequalities.KLS.BKL.Localization.drift μ hc) (FunctionalInequalities.KLS.BKL.Localization.noise μ hc)
          (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n =>
            FunctionalInequalities.Analysis.BakryEmery.cumulant
              (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n)))
              (r + 1) (dirs K)) p =
        -(((r : ℝ) + 1) *
            FunctionalInequalities.Analysis.BakryEmery.cumulant
              (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n)))
              (r + 1) (dirs K) +
          FunctionalInequalities.KLS.BKL.lowerDrift
            (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n)))
            (dirs K) 0)
    have h := FunctionalInequalities.KLS.BKL.Localization.generator_cumulant_posterior_408915f μ hc hiso
      (show 3 ≤ r + 1 by omega) (dirs K) 0 p
    rw [FunctionalInequalities.KLS.BKL.Localization.generator, FunctionalInequalities.Probability.Diffusion.diffusionGenerator_eq_vectorGenerator] at h
    simpa only [Nat.cast_succ] using h
  have hv :
      FunctionalInequalities.Probability.Diffusion.vectorGenerator (FunctionalInequalities.KLS.BKL.Localization.drift μ hc) (FunctionalInequalities.KLS.BKL.Localization.noise μ hc) G p =
        (-1, -(((r : ℝ) + 1) • FunctionalInequalities.KLS.BKL.Localization.energyTensor μ hc p r u + FunctionalInequalities.KLS.BKL.Localization.lowerTensor μ hc p r u)) := by
    change
      FunctionalInequalities.Probability.Diffusion.vectorGenerator (FunctionalInequalities.KLS.BKL.Localization.drift μ hc) (FunctionalInequalities.KLS.BKL.Localization.noise μ hc)
        (fun q => (G₁ q, G₂ q)) p = _
    rw [FunctionalInequalities.Probability.Diffusion.vectorGenerator_prodMk (FunctionalInequalities.KLS.BKL.Localization.drift μ hc) (FunctionalInequalities.KLS.BKL.Localization.noise μ hc) h₁ h₂, hv₁, hv₂]
  have hn (k : Fin n) :
      FunctionalInequalities.KLS.BKL.Localization.noise μ hc p k = (P (EuclideanSpace.basisFun (Fin n) ℝ k), 0) := by
    simp only [FunctionalInequalities.KLS.BKL.Localization.noise, P, EuclideanSpace.basisFun_apply]
  have hd₁ (k : Fin n) :
      fderiv ℝ G₁ p (FunctionalInequalities.KLS.BKL.Localization.noise μ hc p k) = FunctionalInequalities.KLS.BKL.Localization.conjugatedNoiseOperator μ hc p k :=
    FunctionalInequalities.Probability.Diffusion.fderiv_clm_comp_apply_vec L (hA.differentiableAt (by norm_num))
      (FunctionalInequalities.KLS.BKL.Localization.noise μ hc p k)
  have hd₂ (k : Fin n) :
      fderiv ℝ G₂ p (FunctionalInequalities.KLS.BKL.Localization.noise μ hc p k) = FunctionalInequalities.KLS.BKL.Localization.noiseTensor μ hc p r u k := by
    rw [FunctionalInequalities.Probability.Diffusion.fderiv_pi_apply_vec
      (fun K => (hK K).differentiableAt (by norm_num)) (FunctionalInequalities.KLS.BKL.Localization.noise μ hc p k)]
    funext K
    change
      fderiv ℝ
          (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n =>
            FunctionalInequalities.Analysis.BakryEmery.cumulant
              (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n)))
              (r + 1) (dirs K)) p (FunctionalInequalities.KLS.BKL.Localization.noise μ hc p k) =
        FunctionalInequalities.KLS.BKL.Localization.noiseTensor μ hc p r u k K
    rw [hn, FunctionalInequalities.KLS.BKL.Localization.fderiv_cumulant_posterior_apply_408915f μ hc
      (show 1 ≤ r + 1 by omega) (dirs K) p
      (P (EuclideanSpace.basisFun (Fin n) ℝ k))]
    exact congrArg
      (FunctionalInequalities.Analysis.BakryEmery.cumulant
        (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n)))
        (r + 1 + 1))
      (Fin.cons_snoc_eq_snoc_cons u
        (fun s => P (EuclideanSpace.basisFun (Fin n) ℝ (K s)))
        (P (EuclideanSpace.basisFun (Fin n) ℝ k))).symm
  have hd (k : Fin n) :
      fderiv ℝ G p (FunctionalInequalities.KLS.BKL.Localization.noise μ hc p k) =
        (FunctionalInequalities.KLS.BKL.Localization.conjugatedNoiseOperator μ hc p k, FunctionalInequalities.KLS.BKL.Localization.noiseTensor μ hc p r u k) := by
    change fderiv ℝ (fun q => (G₁ q, G₂ q)) p (FunctionalInequalities.KLS.BKL.Localization.noise μ hc p k) = _
    rw [FunctionalInequalities.Probability.Diffusion.fderiv_prodMk_apply_vec
      (h₁.differentiableAt (by norm_num))
      (h₂.differentiableAt (by norm_num)) (FunctionalInequalities.KLS.BKL.Localization.noise μ hc p k), hd₁, hd₂]
  rw [heq]
  change FunctionalInequalities.Probability.Diffusion.diffusionGenerator (FunctionalInequalities.KLS.BKL.Localization.drift μ hc) (FunctionalInequalities.KLS.BKL.Localization.noise μ hc) (Φ ∘ G) p = _
  rw [FunctionalInequalities.Probability.Diffusion.diffusionGenerator_comp_of_contDiffAt_408915f
    (FunctionalInequalities.KLS.BKL.Localization.drift μ hc) (FunctionalInequalities.KLS.BKL.Localization.noise μ hc) Φ G p hΦ hG]
  change
    fderiv ℝ Φ (G p) (FunctionalInequalities.Probability.Diffusion.vectorGenerator (FunctionalInequalities.KLS.BKL.Localization.drift μ hc) (FunctionalInequalities.KLS.BKL.Localization.noise μ hc) G p) +
      (1 / 2 : ℝ) * ∑ k,
        fderiv ℝ (fderiv ℝ Φ) (G p)
          (fderiv ℝ G p (FunctionalInequalities.KLS.BKL.Localization.noise μ hc p k))
          (fderiv ℝ G p (FunctionalInequalities.KLS.BKL.Localization.noise μ hc p k)) = _
  rw [hv, hGp]
  simp only [hd]
  rfl
