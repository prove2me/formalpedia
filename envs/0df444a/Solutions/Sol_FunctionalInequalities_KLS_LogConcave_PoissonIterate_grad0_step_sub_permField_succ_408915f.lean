-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0_step_sub_permField_succ_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:53:13.733336+00:00
-- url     : https://prove2.me/submissions/2f6bcfda-9fbb-4e6c-bc9c-ea34b31d5548

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
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_PoissonIterate_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_PoissonIterate_Permutation
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_FromBorell
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Hessian
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Markov
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_OperatorCore
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
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
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
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_grad0_sub_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_existsUnique_centered_adjointComp_eq_408915f

section
noncomputable section
open MeasureTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.L2
end FunctionalInequalities.L2
open FunctionalInequalities FunctionalInequalities.L2
variable {α : Type*} [MeasurableSpace α]
/-- The Hilbert-space mean agrees with the integral of any representative supplied by `Lp`. -/
theorem FunctionalInequalities.L2.mean_eq_integral (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ f = ∫ x, f x ∂(μ : Measure α) := by
  rw [mean, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [const_coeFn μ 1] with x hx
  simp [hx]
/-- Probability normalization makes the mean of a constant equal to that constant. -/
@[simp]
theorem FunctionalInequalities.L2.mean_const (μ : ProbabilityMeasure α) (c : ℝ) : mean μ (const μ c) = c := by
  rw [mean_eq_integral]
  calc
    (∫ x, const μ c x ∂(μ : Measure α)) = ∫ _ : α, c ∂(μ : Measure α) :=
      integral_congr_ae (const_coeFn μ c)
    _ = c := by simp
/-- The mean of zero is zero. -/
@[simp]
theorem FunctionalInequalities.L2.mean_zero (μ : ProbabilityMeasure α) : mean μ 0 = 0 := by
  simp [mean]
/-- The mean preserves addition. -/
@[simp]
theorem FunctionalInequalities.L2.mean_add (μ : ProbabilityMeasure α) (f g : Lp ℝ 2 (μ : Measure α)) :
    mean μ (f + g) = mean μ f + mean μ g := by
  rw [mean, inner_add_left]
  rfl
/-- The mean preserves real scalar multiplication. -/
@[simp]
theorem FunctionalInequalities.L2.mean_smul (μ : ProbabilityMeasure α) (c : ℝ) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ (c • f) = c * mean μ f := by
  rw [mean, inner_smul_left]
  rfl
/-- The mean preserves subtraction. -/
@[simp]
theorem FunctionalInequalities.L2.mean_sub (μ : ProbabilityMeasure α) (f g : Lp ℝ 2 (μ : Measure α)) :
    mean μ (f - g) = mean μ f - mean μ g := by
  rw [mean, inner_sub_left]
  rfl
/-- Centering commutes with real scalar multiplication. -/
@[simp]
theorem FunctionalInequalities.L2.center_smul (μ : ProbabilityMeasure α) (c : ℝ) (f : Lp ℝ 2 (μ : Measure α)) :
    center μ (c • f) = c • center μ f := by
  simp only [center, mean_smul, const_smul, smul_sub]
/-- A centered `L²` element has mean zero. -/
@[simp]
theorem FunctionalInequalities.L2.mean_center (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ (center μ f) = 0 := by
  simp [center]
end
end
end
end

section
noncomputable section
open scoped LinearPMap
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Semigroup
end FunctionalInequalities.Analysis.Semigroup
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Semigroup
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
/-- Points of the domain of `T†T` are points of the domain of `T`. -/
theorem FunctionalInequalities.Analysis.Semigroup.mem_domain_of_mem_adjointComp_domain (T : H₀ →ₗ.[ℝ] H₁) (x : (adjointComp T).domain) :
    (x : H₀) ∈ T.domain :=
  x.2.2
end
end
end
end
end

section
noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup
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
namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate
end FunctionalInequalities.KLS.LogConcave.PoissonIterate
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.PoissonIterate
section General
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
variable {ν : ProbabilityMeasure V} (T : Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V))
/-- The total gradient agrees with `T` on its domain. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.weakGrad_of_mem {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ T.domain) :
    weakGrad T u = T ⟨u, hu⟩ :=
  dif_pos hu
/-- The total generator agrees with `T†T` on its domain. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen_of_mem {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (adjointComp T).domain) :
    gen T u = adjointComp T ⟨u, hu⟩ :=
  dif_pos hu
/-- The total gradient of `0` is `0`. -/
@[simp]
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.weakGrad_zero : weakGrad T 0 = 0 := by
  rw [weakGrad_of_mem T T.domain.zero_mem]
  exact LinearPMap.map_zero T
/-- The total gradient is homogeneous, on and off the domain of `T`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.weakGrad_smul (c : ℝ) (u : Lp ℝ 2 (ν : Measure V)) :
    weakGrad T (c • u) = c • weakGrad T u := by
  by_cases hu : u ∈ T.domain
  · rw [weakGrad_of_mem T (T.domain.smul_mem c hu), weakGrad_of_mem T hu]
    exact LinearPMap.map_smul T c ⟨u, hu⟩
  · by_cases hc : c = 0
    · subst hc
      simp
    · have hcu : c • u ∉ T.domain := fun h => hu (by
        simpa [smul_smul, hc] using T.domain.smul_mem c⁻¹ h)
      simp [weakGrad, hu, hcu]
/-- The total generator is homogeneous on the domain of `T†T`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen_smul (c : ℝ) {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (adjointComp T).domain) :
    gen T (c • u) = c • gen T u := by
  rw [gen_of_mem T ((adjointComp T).domain.smul_mem c hu), gen_of_mem T hu]
  exact LinearPMap.map_smul (adjointComp T) c ⟨u, hu⟩
/-- The total generator is additive on the domain of `T†T`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen_add {u v : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (adjointComp T).domain)
    (hv : v ∈ (adjointComp T).domain) : gen T (u + v) = gen T u + gen T v := by
  rw [gen_of_mem T ((adjointComp T).domain.add_mem hu hv), gen_of_mem T hu, gen_of_mem T hv]
  exact LinearPMap.map_add (adjointComp T) ⟨u, hu⟩ ⟨v, hv⟩
/-- The centered inverse is always centered (it is `0` when no centered preimage exists). -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.mean_centeredInv (g : Lp ℝ 2 (ν : Measure V)) : L2.mean ν (centeredInv T g) = 0 := by
  unfold centeredInv
  split_ifs with h
  · exact h.choose_spec.1
  · exact L2.mean_zero ν
/-- If a centered preimage of `g` under `T†T` exists, the centered inverse is one. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.centeredInv_spec_of_exists {g : Lp ℝ 2 (ν : Measure V)}
    (h : ∃ u : (adjointComp T).domain,
      L2.mean ν (u : Lp ℝ 2 (ν : Measure V)) = 0 ∧ adjointComp T u = g) :
    ∃ hu : centeredInv T g ∈ (adjointComp T).domain, adjointComp T ⟨_, hu⟩ = g := by
  have hc : centeredInv T g = (h.choose : Lp ℝ 2 (ν : Measure V)) := by
    unfold centeredInv
    rw [dif_pos h]
  rw [hc]
  exact ⟨h.choose.2, h.choose_spec.2⟩
variable [FiniteDimensional ℝ V]
/-- The components of `∇₀h` are centered. -/
@[simp]
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.mean_grad0 {k : ℕ} (h : Field ν k) (J : Fin (k + 1) → Fin (Module.finrank ℝ V)) :
    L2.mean ν (grad0 T h J) = 0 :=
  L2.mean_center ν _
end General
section HeatModel
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
  {C : NNReal} (hC : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
include hνU hU hC in
/-- **BKL Lemma 2.1 for the total centered inverse.** For centered `g`, `centeredInv T̄ g` lies in
`D(A)` and solves `A u = g`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.centeredInv_spec {g : Lp ℝ 2 (ν : Measure V)} (hg : L2.mean ν g = 0) :
    ∃ hu : centeredInv T̄ g ∈ (adjointComp T̄).domain, adjointComp T̄ ⟨_, hu⟩ = g :=
  centeredInv_spec_of_exists _
    (existsUnique_centered_adjointComp_eq_408915f m hν hi hνU hU hC g hg).exists
include hνU hU hC in
/-- For centered `g`, `(-L)⁻¹ g ∈ D(A)`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.centeredInv_mem_domain {g : Lp ℝ 2 (ν : Measure V)} (hg : L2.mean ν g = 0) :
    centeredInv T̄ g ∈ (adjointComp T̄).domain :=
  (centeredInv_spec m hν hi hνU hU hC hg).1
include hνU hU hC in
/-- For centered `g`, `-L (-L)⁻¹ g = g`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen_centeredInv {g : Lp ℝ 2 (ν : Measure V)} (hg : L2.mean ν g = 0) :
    gen T̄ (centeredInv T̄ g) = g := by
  obtain ⟨hu, hAu⟩ := centeredInv_spec m hν hi hνU hU hC hg
  rw [gen_of_mem _ hu, hAu]
include hνU hU hC in
/-- Uniqueness: a centered `u ∈ D(A)` with `A u = g` is the centered inverse of `g`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.centeredInv_eq_of_gen_eq {g u : Lp ℝ 2 (ν : Measure V)} (hg : L2.mean ν g = 0)
    (hu : u ∈ (adjointComp T̄).domain) (hmean : L2.mean ν u = 0) (hgen : gen T̄ u = g) :
    centeredInv T̄ g = u := by
  obtain ⟨hv, hAv⟩ := centeredInv_spec m hν hi hνU hU hC hg
  have huniq := (existsUnique_centered_adjointComp_eq_408915f m hν hi hνU hU hC g hg).unique
    (y₁ := ⟨_, hv⟩) (y₂ := ⟨u, hu⟩) ⟨mean_centeredInv (T̄) g, hAv⟩
    ⟨hmean, by rw [← gen_of_mem _ hu, hgen]⟩
  exact congrArg Subtype.val huniq
include hνU hU hC in
/-- The centered inverse is homogeneous on centered inputs. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.centeredInv_smul (c : ℝ) {g : Lp ℝ 2 (ν : Measure V)} (hg : L2.mean ν g = 0) :
    centeredInv T̄ (c • g) = c • centeredInv T̄ g := by
  have hmem := centeredInv_mem_domain m hν hi hνU hU hC hg
  refine centeredInv_eq_of_gen_eq m hν hi hνU hU hC (by rw [L2.mean_smul, hg, mul_zero])
    ((adjointComp T̄).domain.smul_mem c hmem) (by rw [L2.mean_smul, mean_centeredInv, mul_zero])
    ?_
  rw [gen_smul _ c hmem, gen_centeredInv m hν hi hνU hU hC hg]
include hνU hU hC in
/-- The centered inverse is additive on centered inputs. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.centeredInv_add {g₁ g₂ : Lp ℝ 2 (ν : Measure V)} (hg₁ : L2.mean ν g₁ = 0)
    (hg₂ : L2.mean ν g₂ = 0) :
    centeredInv T̄ (g₁ + g₂) = centeredInv T̄ g₁ + centeredInv T̄ g₂ := by
  have h₁ := centeredInv_mem_domain m hν hi hνU hU hC hg₁
  have h₂ := centeredInv_mem_domain m hν hi hνU hU hC hg₂
  refine centeredInv_eq_of_gen_eq m hν hi hνU hU hC (by rw [L2.mean_add, hg₁, hg₂, add_zero])
    ((adjointComp T̄).domain.add_mem h₁ h₂)
    (by rw [L2.mean_add, mean_centeredInv, mean_centeredInv, add_zero]) ?_
  rw [gen_add _ h₁ h₂, gen_centeredInv m hν hi hνU hU hC hg₁,
    gen_centeredInv m hν hi hνU hU hC hg₂]
include hνU hU hC in
/-- The components of one step lie in `D(A)`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.step_mem_domain {k : ℕ} (h : Field ν k) (J : Fin (k + 1) → Fin (Module.finrank ℝ V)) :
    step T̄ h J ∈ (adjointComp T̄).domain :=
  (adjointComp T̄).domain.smul_mem _
    (centeredInv_mem_domain m hν hi hνU hU hC (mean_grad0 (T̄) h J))
end HeatModel
end
end
end
end
end
end

noncomputable section
open MeasureTheory Finset
open FunctionalInequalities.Analysis.Semigroup
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
namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate
end FunctionalInequalities.KLS.LogConcave.PoissonIterate
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.PoissonIterate
section Positions
/-- `finRotate` commutes with `Fin.succ` below the last position. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.finRotate_succ_eq {k : ℕ} (ℓ : Fin (k + 1)) (hℓ : ℓ.val + 1 < k + 1) :
    finRotate (k + 2) ℓ.succ = (finRotate (k + 1) ℓ).succ := by
  have h1 : ℓ.succ ≠ Fin.last (k + 1) := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_last] at this
    omega
  have h2 : ℓ ≠ Fin.last k := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last] at this
    omega
  ext
  rw [coe_finRotate_of_ne_last h1, Fin.val_succ, Fin.val_succ, coe_finRotate_of_ne_last h2]
/-- `τ_{ℓ+1}` fixes the first position. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.swap_succ_apply_zero {k : ℕ} (ℓ : Fin (k + 1)) (hℓ : ℓ.val + 1 < k + 1) :
    Equiv.swap ℓ.succ (finRotate (k + 2) ℓ.succ) 0 = 0 := by
  rw [finRotate_succ_eq ℓ hℓ]
  exact Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _).symm (Fin.succ_ne_zero _).symm
/-- `τ_{ℓ+1}` acts as `τ_ℓ` on the shifted positions. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.swap_succ_apply_succ {k : ℕ} (ℓ : Fin (k + 1)) (hℓ : ℓ.val + 1 < k + 1)
    (i : Fin (k + 1)) :
    Equiv.swap ℓ.succ (finRotate (k + 2) ℓ.succ) i.succ =
      (Equiv.swap ℓ (finRotate (k + 1) ℓ) i).succ := by
  rw [finRotate_succ_eq ℓ hℓ]
  exact (Fin.succ_injective _).swap_apply _ _ _
end Positions
section General
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] {ν : ProbabilityMeasure V}
  (T : Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V))
/-- A permutation `σ'` of `k + 1` positions that fixes the first one and acts as `σ` on the
others commutes with `∇₀`: `σ' ∇₀u = ∇₀(σ u)`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField_grad0 {k : ℕ} (σ : Equiv.Perm (Fin k)) (σ' : Equiv.Perm (Fin (k + 1)))
    (h0 : σ' 0 = 0) (hs : ∀ i, σ' i.succ = (σ i).succ) (u : Field ν k) :
    permField σ' (grad0 T u) = grad0 T (permField σ u) := by
  funext J
  have hJ0 : (J ∘ σ') 0 = J 0 := by simp [h0]
  have hJt : Fin.tail (J ∘ σ') = Fin.tail J ∘ σ := by
    funext i
    simp [Fin.tail, hs]
  simp only [permField, grad0, gradField, hJ0, hJt]
/-- `∇₀` is homogeneous. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0_smul {k : ℕ} (c : ℝ) (u : Field ν k) : grad0 T (c • u) = c • grad0 T u := by
  funext J
  have hL : ∀ (L : V →L[ℝ] ℝ) (a : Lp V 2 (ν : Measure V)),
      L.compLp (c • a) = c • L.compLp a :=
    fun L a => (L.compLpₗ 2 (ν : Measure V)).map_smul c a
  simp only [grad0, gradField, partialDeriv, Pi.smul_apply, weakGrad_smul, hL, L2.center_smul]
end General
section HeatModel
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
  {C : NNReal} (hC : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
include hνU hU hC in
/-- The centered inverse commutes with subtraction on centered inputs. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.centeredInv_sub {g₁ g₂ : Lp ℝ 2 (ν : Measure V)} (hg₁ : L2.mean ν g₁ = 0)
    (hg₂ : L2.mean ν g₂ = 0) :
    centeredInv T̄ (g₁ - g₂) = centeredInv T̄ g₁ - centeredInv T̄ g₂ := by
  have hneg : L2.mean ν ((-1 : ℝ) • g₂) = 0 := by rw [L2.mean_smul, hg₂, mul_zero]
  rw [sub_eq_add_neg, ← neg_one_smul ℝ g₂, centeredInv_add m hν hi hνU hU hC hg₁ hneg,
    centeredInv_smul m hν hi hνU hU hC _ hg₂, neg_one_smul, ← sub_eq_add_neg]
namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate
end FunctionalInequalities.KLS.LogConcave.PoissonIterate
open FunctionalInequalities.KLS.LogConcave.PoissonIterate in
include hνU hU hC in
/-- **BKL (42).** For `h' = α (-L)⁻¹ ∇₀h` (`α = scale h`) and `ℓ + 1 < k + 1`, the transposition
`τ_{ℓ+1}` of the positions `ℓ + 1, ℓ + 2` of `∇₀h'` is the transposition `τ_ℓ` of `∇₀h`:
`∇₀h' - τ_{ℓ+1} ∇₀h' = α ∇₀(-L)⁻¹(∇₀h - τ_ℓ ∇₀h)`. -/
theorem solution {k : ℕ} (h : FunctionalInequalities.KLS.LogConcave.PoissonIterate.Field ν k) (ℓ : Fin (k + 1))
    (hℓ : ℓ.val + 1 < k + 1) :
    FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h) -
        FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField (Equiv.swap ℓ.succ (finRotate (k + 2) ℓ.succ)) (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h)) =
      FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ h • FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.invField T̄
        (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ h - FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField (Equiv.swap ℓ (finRotate (k + 1) ℓ)) (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ h))) := by
  set τ := Equiv.swap ℓ (finRotate (k + 1) ℓ)
  have hdom : ∀ J, FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h J ∈ (T̄).domain := fun J =>
    FunctionalInequalities.Analysis.Semigroup.mem_domain_of_mem_adjointComp_domain _ ⟨_, FunctionalInequalities.KLS.LogConcave.PoissonIterate.step_mem_domain m hν hi hνU hU hC h J⟩
  rw [FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField_grad0 _ τ _ (swap_succ_apply_zero ℓ hℓ) (swap_succ_apply_succ ℓ hℓ),
    ← FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0_sub_408915f _ (v := FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField τ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h)) hdom (fun J => hdom _)]
  have e : FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h - FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField τ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h) =
      FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ h • FunctionalInequalities.KLS.LogConcave.PoissonIterate.invField T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ h - FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField τ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ h)) := by
    funext I
    simp only [FunctionalInequalities.KLS.LogConcave.PoissonIterate.step, Pi.sub_apply, Pi.smul_apply, FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField, FunctionalInequalities.KLS.LogConcave.PoissonIterate.invField]
    rw [centeredInv_sub m hν hi hνU hU hC (FunctionalInequalities.KLS.LogConcave.PoissonIterate.mean_grad0 _ h _) (FunctionalInequalities.KLS.LogConcave.PoissonIterate.mean_grad0 _ h _), smul_sub]
  rw [e, FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0_smul]
