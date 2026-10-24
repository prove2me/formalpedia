-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.PoissonIterate.exists_symm_normSq_grad0_step_sub_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:55:58.324991+00:00
-- url     : https://prove2.me/submissions/b94201fc-0f10-442d-8625-637590f33076

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
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_gradField_gradField_comp_swap_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_inv_le_scale_sq_step_408915f
import Theorems.Thm_FunctionalInequalities_L2_inner_center_center_408915f
import Theorems.Thm_FunctionalInequalities_L2_sum_norm_sq_compLp_innerSL_408915f

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
/-- Embedding constants into `L²` preserves addition. -/
@[simp]
theorem FunctionalInequalities.L2.const_add (μ : ProbabilityMeasure α) (c d : ℝ) :
    const μ (c + d) = const μ c + const μ d :=
  map_add (Lp.const 2 (μ : Measure α)) c d
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
/-- Centering preserves addition. -/
@[simp]
theorem FunctionalInequalities.L2.center_add (μ : ProbabilityMeasure α) (f g : Lp ℝ 2 (μ : Measure α)) :
    center μ (f + g) = center μ f + center μ g := by
  simp only [center, mean_add, const_add]
  abel
/-- Centering commutes with real scalar multiplication. -/
@[simp]
theorem FunctionalInequalities.L2.center_smul (μ : ProbabilityMeasure α) (c : ℝ) (f : Lp ℝ 2 (μ : Measure α)) :
    center μ (c • f) = c • center μ f := by
  simp only [center, mean_smul, const_smul, smul_sub]
end
end
end
end

section
noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace Classical
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
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ν : ProbabilityMeasure V} (T : Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V))
omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- `normSq` is nonnegative. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_nonneg {k : ℕ} (u : Field ν k) : 0 ≤ normSq u :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _
end
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
/-- `normSq` is quadratic: `‖c u‖² = c² ‖u‖²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_smul {k : ℕ} (c : ℝ) (u : Field ν k) : normSq (c • u) = c ^ 2 * normSq u := by
  unfold normSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
variable [FiniteDimensional ℝ V]
/-- Parseval for the weak partial derivatives: `Σ_j ‖∂_j u‖² = ‖∇u‖²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sum_norm_sq_partialDeriv (u : Lp ℝ 2 (ν : Measure V)) :
    ∑ j, ‖partialDeriv T j u‖ ^ 2 = ‖weakGrad T u‖ ^ 2 :=
  L2.sum_norm_sq_compLp_innerSL_408915f (stdOrthonormalBasis ℝ V) (weakGrad T u)
/-- The energy of a field is the sum of the squared gradient norms of its components. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy_eq_sum {k : ℕ} (u : Field ν k) :
    energy T u = ∑ I, ‖weakGrad T (u I)‖ ^ 2 := by
  unfold energy normSq gradField
  rw [← (Fin.consEquiv fun _ : Fin (k + 1) => Fin (Module.finrank ℝ V)).sum_comp,
    Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => ?_
  simp only [Fin.consEquiv_apply, Fin.cons_zero]
  exact sum_norm_sq_partialDeriv T (u I)
/-- The energy is quadratic: `‖∇(c u)‖² = c² ‖∇u‖²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy_smul {k : ℕ} (c : ℝ) (u : Field ν k) : energy T (c • u) = c ^ 2 * energy T u := by
  rw [energy_eq_sum, energy_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Pi.smul_apply, weakGrad_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
end General
end
end
end
end
end
end

noncomputable section
open MeasureTheory Filter Topology
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
variable {α : Type*} [MeasurableSpace α] {ν : ProbabilityMeasure α}
/-- Centering does not increase the `L²` norm: `‖u - ∫u‖² ≤ ‖u‖²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_center_sq_le (u : Lp ℝ 2 (ν : Measure α)) :
    ‖L2.center ν u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, L2.inner_center_center_408915f]
  nlinarith [sq_nonneg (L2.mean ν u)]
/-- Centering is linear: `center (x - c y) = center x - c center y`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.center_sub_smul (x y : Lp ℝ 2 (ν : Measure α)) (c : ℝ) :
    L2.center ν (x - c • y) = L2.center ν x - c • L2.center ν y := by
  rw [sub_eq_add_neg, ← neg_smul, L2.center_add, L2.center_smul, neg_smul, ← sub_eq_add_neg]
end General
section Scale
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] {ν : ProbabilityMeasure V}
  (T : Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V))
/-- The normalizing coefficient `α` is nonnegative. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale_nonneg {k : ℕ} (h : Field ν k) : 0 ≤ scale T h := by
  unfold scale
  split_ifs
  exacts [le_rfl, Real.sqrt_nonneg _]
end Scale
section HeatModel
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hUt : U.HasTemperateGrowth)
  (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
  {C : NNReal} (hC : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
omit [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- A potential of temperate growth is `C²`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.contDiff_two (hUt : U.HasTemperateGrowth) : ContDiff ℝ 2 U :=
  hUt.1.of_le (WithTop.coe_le_coe.mpr le_top)
/-- Centering componentwise is a contraction of `normSq`: for `α = scale h`,
`‖∇₀h' - α⁻¹ center ∇²h‖² ≤ ‖∇h' - α⁻¹ ∇²h‖²`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_grad0_step_sub_le {k : ℕ} (h : Field ν k) :
    normSq (grad0 T̄ (step T̄ h) -
        fun J => (scale T̄ h)⁻¹ • L2.center ν (gradField T̄ (gradField T̄ h) J)) ≤
      normSq (gradField T̄ (step T̄ h) - (scale T̄ h)⁻¹ • gradField T̄ (gradField T̄ h)) := by
  unfold normSq
  refine Finset.sum_le_sum fun J _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, grad0]
  rw [← center_sub_smul]
  exact norm_center_sq_le _
namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate
end FunctionalInequalities.KLS.LogConcave.PoissonIterate
open FunctionalInequalities.KLS.LogConcave.PoissonIterate in
include hνU hUt hexp hC in
/-- **BKL Lemma 3.2 for one step**, with `λ = 1/C`. For a field `h` with components in `D(A)`,
`h' = α (-L)⁻¹ ∇₀h` is within `C χ` of a field symmetric in its first two index positions:
`S = α⁻¹ (∇²h - ∫∇²h)` (and `S = 0` when `α = 0`) satisfies `‖∇₀h' - S‖² ≤ C χ`. -/
theorem solution (hCpos : 0 < C) {k : ℕ} (h : FunctionalInequalities.KLS.LogConcave.PoissonIterate.Field ν k)
    (hh : ∀ I, h I ∈ (FunctionalInequalities.Analysis.Semigroup.adjointComp T̄).domain) :
    ∃ S : FunctionalInequalities.KLS.LogConcave.PoissonIterate.Field ν (k + 2), (∀ J, S (J ∘ Equiv.swap 0 1) = S J) ∧
      FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h) - S) ≤ (C : ℝ) * FunctionalInequalities.KLS.LogConcave.PoissonIterate.defect T̄ h := by
  have hU := contDiff_two hUt
  refine ⟨fun J => (FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ h)⁻¹ • FunctionalInequalities.L2.center ν (FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ h) J),
    fun J => ?_, (normSq_grad0_step_sub_le m hν hi h).trans ?_⟩
  · simp only [FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField_gradField_comp_swap_408915f m hν hi hνU hUt hexp h hh J]
  have hdef : 0 ≤ FunctionalInequalities.KLS.LogConcave.PoissonIterate.defect T̄ h := FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_nonneg _
  rcases (FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale_nonneg (T̄) h).eq_or_lt with h0 | hpos
  · rw [← h0, inv_zero, zero_smul, sub_zero,
      show FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h)) = FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h) from rfl, FunctionalInequalities.KLS.LogConcave.PoissonIterate.step, FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy_smul,
      ← h0]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    exact mul_nonneg C.2 hdef
  · have e : FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h) - (FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ h)⁻¹ • FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ h) =
        (-(FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ h)⁻¹) •
          (FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ h) - FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ h • FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h)) := by
      rw [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hpos.ne', neg_smul, neg_smul, one_smul]
      abel
    have hinv : (FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ h ^ 2)⁻¹ ≤ (C : ℝ) :=
      inv_le_of_inv_le₀ (NNReal.coe_pos.mpr hCpos)
        (FunctionalInequalities.KLS.LogConcave.PoissonIterate.inv_le_scale_sq_step_408915f m hν hi hνU hU hC hCpos h hpos)
    rw [e, FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_smul, neg_sq, inv_pow]
    exact mul_le_mul_of_nonneg_right hinv hdef
