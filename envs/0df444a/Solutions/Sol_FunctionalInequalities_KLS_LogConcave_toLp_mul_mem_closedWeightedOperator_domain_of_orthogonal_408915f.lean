-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:35:17.936836+00:00
-- url     : https://prove2.me/submissions/37621648-f77a-44cf-acbd-3be32210661c

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointClosure
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointComp
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Contraction
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_MeanValue
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Laws
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
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_WeakDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Closable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_WeightedGradient_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_OperatorCore
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Closure
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Multiplier
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_BoundedMultiplier
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
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
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
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
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_Analysis_Mollification_lintegral_enorm_convolution_sq_le_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_Mollification_tendsto_eLpNorm_convolution_sub_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integral_laplacian_mul_convolution_eq_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integral_laplacian_mul_tiltedDensity_mul_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_norm_toLp_smul_gradient_le_408915f

section
noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
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
universe u
section DifferentialTools
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Gradient
variable [CompleteSpace E]
/-- Product rule for the gradient. -/
theorem FunctionalInequalities.Analysis.BakryEmery.gradient_mul {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => f y * g y) x = f x • gradient g x + g x • gradient f x := by
  unfold gradient
  rw [fderiv_fun_mul hf hg, map_add, map_smulₛₗ, map_smulₛₗ]
  simp
/-- Difference rule for the gradient. -/
theorem FunctionalInequalities.Analysis.BakryEmery.gradient_sub {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => f y - g y) x = gradient f x - gradient g x := by
  unfold gradient
  rw [fderiv_fun_sub hf hg, map_sub]
end Gradient
end DifferentialTools
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
open Energy
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section FullDimensional
variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
/-- `T̄` sends a test class to the class of its weighted gradient. This is the general-test form
of `KLS.LogConcave.closedWeightedOperator_toLp_eq`. -/
theorem FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_apply_toLp (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {g : V → ℝ}
    (h : WeightedGradient.IsTest ν B g) :
    hν.closedWeightedOperator m B hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain_of_isTest m B hi h⟩ =
      h.memLp_apply.toLp (WeightedGradient.apply B g) := by
  have hmem := WeightedGradient.toLp_mem_domain_operator ν B (hν.absolutelyContinuous_haar m hi) h
  rw [← (LinearPMap.le_closure (hν.weightedOperator m B hi)).2 (x := ⟨_, hmem⟩)
    (y := ⟨_, hν.toLp_mem_closedWeightedOperator_domain_of_isTest m B hi h⟩) rfl,
    WeightedGradient.operator_apply ν B _ (hν.frontier_support_eq_zero hi) h hmem rfl]
end FullDimensional
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Mollification
end FunctionalInequalities.Analysis.Mollification
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Mollification
open FunctionalInequalities.Analysis.BakryEmery
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {m : Measure V} [m.IsAddHaarMeasure]
section Contraction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (φ : ContDiffBump (0 : V))
/-- `L²` contraction of the mollifier in `eLpNorm` form. -/
theorem FunctionalInequalities.Analysis.Mollification.eLpNorm_convolution_le {f : V → E} (hf : AEStronglyMeasurable f m) :
    eLpNorm (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) 2 m ≤ eLpNorm f 2 m := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact ENNReal.rpow_le_rpow (lintegral_enorm_convolution_sq_le_408915f φ hf) (by norm_num)
/-- The mollification of a locally integrable function is continuous. -/
theorem FunctionalInequalities.Analysis.Mollification.continuous_convolution {f : V → E} (hf : LocallyIntegrable f m) :
    Continuous (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) :=
  HasCompactSupport.continuous_convolution_left _ (φ.hasCompactSupport_normed (μ := m))
    φ.continuous_normed hf
/-- The mollification of an `L²` function is again `L²`. -/
theorem FunctionalInequalities.Analysis.Mollification.memLp_convolution {f : V → E} (hf : MemLp f 2 m) :
    MemLp (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) 2 m :=
  ⟨(continuous_convolution φ (hf.locallyIntegrable one_le_two)).aestronglyMeasurable,
    (eLpNorm_convolution_le φ hf.1).trans_lt hf.2⟩
end Contraction
end
end
end
end
end

noncomputable section
open MeasureTheory Filter Topology Metric InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Mollification
open scoped ContDiff RealInnerProductSpace Convolution ENNReal
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
open Energy Energy.WeightedGradient
section Generic
variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
/-- A pointwise bound `‖f x‖ ≤ C ‖g x‖` gives `eLpNorm f ≤ C eLpNorm g`. -/
private theorem FunctionalInequalities.KLS.LogConcave.eLpNorm_le_of_norm_le {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : α → E} {g : α → F} {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, ‖f x‖ ≤ C * ‖g x‖) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal C * eLpNorm g 2 μ := by
  refine (eLpNorm_mono_real h).trans (le_of_eq ?_)
  have : (fun x => C * ‖g x‖) = C • fun x => ‖g x‖ := rfl
  rw [this, eLpNorm_const_smul, eLpNorm_norm, Real.enorm_of_nonneg hC]
end Generic
section Pointwise
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
/-- The pairing of a compactly supported field with any field has compact support. -/
private theorem FunctionalInequalities.KLS.LogConcave.hasCompactSupport_inner_left {f g : V → V} (hf : HasCompactSupport f) :
    HasCompactSupport fun x => ⟪f x, g x⟫ := by
  refine HasCompactSupport.of_support_subset_isCompact hf fun x hx => subset_tsupport _ ?_
  rw [Function.mem_support] at hx ⊢
  intro hz
  exact hx (by rw [hz, inner_zero_left])
variable [FiniteDimensional ℝ V]
variable [CompleteSpace V]
omit [FiniteDimensional ℝ V] in
/-- The gradient vanishes outside the closed support. -/
private theorem FunctionalInequalities.KLS.LogConcave.gradient_eq_zero_of_notMem_tsupport {f : V → ℝ} {y : V} (hy : y ∉ tsupport f) :
    gradient f y = 0 := by
  have h : fderiv ℝ f y = 0 := by
    by_contra h
    exact hy (support_fderiv_subset (𝕜 := ℝ) h)
  rw [gradient, h, map_zero]
end Pointwise
section Haar
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (m : Measure V) [m.IsAddHaarMeasure]
omit [InnerProductSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] [m.IsAddHaarMeasure] in
private theorem FunctionalInequalities.KLS.LogConcave.tendsto_mollifier_rOut :
    Tendsto (fun n => (FunctionalInequalities.KLS.LogConcave.mollifier (V := V) n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat
omit [InnerProductSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] [m.IsAddHaarMeasure] in
private theorem FunctionalInequalities.KLS.LogConcave.mollifier_rOut_le_one (n : ℕ) : (FunctionalInequalities.KLS.LogConcave.mollifier (V := V) n).rOut ≤ 1 := by
  change (1 : ℝ) / ((n : ℝ) + 1) ≤ 1
  exact div_le_one_of_le₀ (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]) (by positivity)
end Haar
section Density
variable {V : Type*} [MeasurableSpace V] {ν : ProbabilityMeasure V} (m : Measure V) {U : V → ℝ}
/-- `exp (-U)` is `m`-integrable when `m.tilted (-U)` is a probability measure. -/
private theorem FunctionalInequalities.KLS.LogConcave.integrable_exp_neg (hνU : (ν : Measure V) = m.tilted (-U)) :
    Integrable (fun x => Real.exp ((-U) x)) m := by
  by_contra h
  have h0 : (ν : Measure V) = 0 := by rw [hνU]; exact tilted_of_not_integrable h
  have h1 := measure_univ (μ := (ν : Measure V))
  rw [h0] at h1
  simp at h1
private theorem FunctionalInequalities.KLS.LogConcave.integral_exp_neg_pos [NeZero m] (hνU : (ν : Measure V) = m.tilted (-U)) :
    0 < ∫ y, Real.exp ((-U) y) ∂m :=
  integral_exp_pos (integrable_exp_neg m hνU)
private theorem FunctionalInequalities.KLS.LogConcave.tiltedDensity_pos [NeZero m] (hνU : (ν : Measure V) = m.tilted (-U)) (x : V) :
    0 < FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x :=
  div_pos (Real.exp_pos _) (integral_exp_neg_pos m hνU)
/-- `1 / tiltedDensity = Z exp U`. -/
private theorem FunctionalInequalities.KLS.LogConcave.tiltedDensity_mul_exp [NeZero m] (hνU : (ν : Measure V) = m.tilted (-U))
    (x : V) :
    FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x * ((∫ y, Real.exp ((-U) y) ∂m) * Real.exp (U x)) = 1 := by
  have hZ : (∫ y, Real.exp ((-U) y) ∂m) ≠ 0 := (integral_exp_neg_pos m hνU).ne'
  have hE : Real.exp (U x) ≠ 0 := (Real.exp_pos _).ne'
  unfold FunctionalInequalities.KLS.LogConcave.tiltedDensity
  rw [Pi.neg_apply, Real.exp_neg]
  field_simp
private theorem FunctionalInequalities.KLS.LogConcave.lintegral_eq_tiltedDensity (hνU : (ν : Measure V) = m.tilted (-U))
    (g : V → ℝ≥0∞) :
    ∫⁻ x, g x ∂(ν : Measure V) = ∫⁻ x, ENNReal.ofReal (FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x) * g x ∂m := by
  rw [hνU]
  exact lintegral_tilted _ _
/-- **From `L²(m)` to `L²(ν)`** for a function supported where the density is at most `C`. -/
private theorem FunctionalInequalities.KLS.LogConcave.eLpNorm_tilted_le (hνU : (ν : Measure V) = m.tilted (-U)) {E : Type*}
    [NormedAddCommGroup E] {f : V → E} {C : ℝ}
    (h : ∀ x, f x ≠ 0 → FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x ≤ C) :
    eLpNorm f 2 (ν : Measure V) ≤ ENNReal.ofReal C ^ (1 / 2 : ℝ) * eLpNorm f 2 m := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat]
  rw [lintegral_eq_tiltedDensity m hνU, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ENNReal.rpow_le_rpow (lintegral_mono fun x => ?_) (by norm_num)
  by_cases hx : f x = 0
  · simp [hx]
  · gcongr
    exact h x hx
/-- **From `L²(ν)` to `L²(m)`**: a function dominated by `√(C ρ) |u|` with `u ∈ L²(ν)` is in
`L²(m)`, with the norm bound `√C ‖u‖_{L²(ν)}`. -/
private theorem FunctionalInequalities.KLS.LogConcave.eLpNorm_le_tilted_of_sq_le [NeZero m] (hνU : (ν : Measure V) = m.tilted (-U))
    {E : Type*} [NormedAddCommGroup E] {F : V → E} {C : ℝ} (hC : 0 ≤ C)
    (u : Lp ℝ 2 (ν : Measure V))
    (h : ∀ x, ‖F x‖ ^ 2 ≤ C * FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x * ‖u x‖ ^ 2) :
    eLpNorm F 2 m ≤ ENNReal.ofReal C ^ (1 / 2 : ℝ) * eLpNorm u 2 (ν : Measure V) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat]
  rw [lintegral_eq_tiltedDensity m hνU, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ENNReal.rpow_le_rpow (lintegral_mono fun x => ?_) (by norm_num)
  have hρ := (tiltedDensity_pos m hνU x).le
  have e1 : ‖F x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖F x‖ ^ 2) := by
    rw [← ofReal_norm, ENNReal.rpow_two, ← ENNReal.ofReal_pow (norm_nonneg _)]
  have e2 : ‖u x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖u x‖ ^ 2) := by
    rw [← ofReal_norm, ENNReal.rpow_two, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [e1, e2, ← ENNReal.ofReal_mul hρ, ← ENNReal.ofReal_mul hC, ← mul_assoc]
  exact ENNReal.ofReal_le_ofReal (h x)
end Density
section Tilted
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}
omit [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  [m.IsAddHaarMeasure] in
private theorem FunctionalInequalities.KLS.LogConcave.contDiff_tiltedDensity (hU : ContDiff ℝ 1 U) :
    ContDiff ℝ 1 (FunctionalInequalities.KLS.LogConcave.tiltedDensity m U) :=
  (hU.neg.exp).div_const _
variable (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)
/-- A compactly supported `C¹` function is a weighted-gradient test for the unit weight. -/
private theorem FunctionalInequalities.KLS.LogConcave.isTest_of_contDiff_one {g : V → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) : IsTest ν (ContinuousLinearMap.id ℝ V) g := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨M, hM0, hM⟩ := Energy.Euclidean.exists_bound_fderiv_of_hasCompactSupport hg hgc
    refine ⟨⟨M, hM0⟩, lipschitzWith_of_nnnorm_fderiv_le (hg.differentiable one_ne_zero)
      fun x => ?_⟩
    change ‖fderiv ℝ g x‖ ≤ M
    exact hM x
  · exact hg.continuous.memLp_of_hasCompactSupport hgc
  · rw [apply_id]
    exact (continuous_gradient hg).memLp_of_hasCompactSupport (hasCompactSupport_gradient hgc)
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave in
/-- **Interior regularity of deficiency elements.** For `ν = m.tilted (-U)` with a `C¹` potential
and unit weight, let `u ∈ L²(ν)` be orthogonal to `(A + 1) C_c^∞(V)`, that is,
`⟪A [f], u⟫ + ⟪[f], u⟫ = 0` for every smooth compactly supported `f`. Then every localization
`[χ u]`, `χ ∈ C_c^∞(V)`, lies in the form domain `D(T̄)` of the closed unit-weight gradient.

This is exactly the hypothesis `hreg` of
`exists_seq_smooth_tendsto_adjointComp_of_localRegularity` and
`HeatSemigroup.integral_mul_weakGamma_apply_nonneg_of_localRegularity`.

The proof is the mollification argument for the divergence-form equation
`Δ W = -div (W ∇U) + W` satisfied weakly by `W = ρ u` against the Haar measure: the mollifications
`vₙ = ρₙ ⋆ (η W)` satisfy the same equation with `ρₙ ⋆ (η W ∇U)` in place of `W ∇U`, the
Caccioppoli estimate applied to `vₙ - vₖ` shows that `χ ∇vₙ` is Cauchy in `L²(m)`, and the
`C¹` compactly supported functions `χ vₙ / ρ` are then a graph-Cauchy sequence of tests converging
to `[χ u]` in `L²(ν)`; closedness of `T̄` concludes. No classical derivative of `u` is used. -/
theorem solution
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U) (u : Lp ℝ 2 (ν : Measure V))
    (horth : ∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
      ⟪(FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ : Lp ℝ 2 (ν : Measure V)), u⟫ +
        ⟪((FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f : Lp ℝ 2 (ν : Measure V)), u⟫ = 0)
    {χ : V → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _ ∈
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain := by
  classical
  -- the density, its inverse and their regularity
  have hρpos : ∀ x, 0 < FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x := tiltedDensity_pos m hνU
  have hρc : ContDiff ℝ 1 (FunctionalInequalities.KLS.LogConcave.tiltedDensity m U) := contDiff_tiltedDensity m hU
  set ρinv : V → ℝ := fun x => (∫ y, Real.exp ((-U) y) ∂m) * Real.exp (U x) with hρinv_def
  have hρρinv : ∀ x, FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x * ρinv x = 1 := tiltedDensity_mul_exp m hνU
  have hρinvc : ContDiff ℝ 1 ρinv := contDiff_const.mul hU.exp
  have hρinvd : Differentiable ℝ ρinv := hρinvc.differentiable one_ne_zero
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hχd : Differentiable ℝ χ := hχ1.differentiable one_ne_zero
  have hUc : Continuous (gradient U) := FunctionalInequalities.Analysis.BakryEmery.continuous_gradient hU
  have hmν : m ≪ (ν : Measure V) := by
    rw [hνU]; exact absolutelyContinuous_tilted (integrable_exp_neg m hνU)
  have hum : AEStronglyMeasurable (u : V → ℝ) m := (Lp.aestronglyMeasurable u).mono_ac hmν
  -- the radius and the cutoff `η`, equal to one on `closedBall 0 (R + 1)`
  obtain ⟨R, hR0, hR⟩ := hχc.isBounded.subset_closedBall_lt 0 0
  set η : ContDiffBump (0 : V) := ⟨R + 1, R + 2, by linarith, by linarith⟩ with hη_def
  have hηχ : ∀ x ∈ tsupport χ, η x = 1 := fun x hx =>
    η.one_of_mem_closedBall (closedBall_subset_closedBall (by linarith) (hR hx))
  have hηzero : ∀ x ∉ closedBall (0 : V) (R + 2), η x = 0 := fun x hx => by
    refine η.zero_of_le_dist ?_
    rw [mem_closedBall, not_le] at hx
    exact hx.le
  -- the density-weighted class and its localizations
  set W : V → ℝ := fun x => FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x * u x with hW_def
  set w : V → ℝ := fun x => η x * W x with hw_def
  set G : V → V := fun x => (η x * W x) • gradient U x with hG_def
  have hWm : AEStronglyMeasurable W m := hρc.continuous.aestronglyMeasurable.mul hum
  have hwm : AEStronglyMeasurable w m := η.continuous.aestronglyMeasurable.mul hWm
  have hGm : AEStronglyMeasurable G m :=
    (η.continuous.aestronglyMeasurable.mul hWm).smul hUc.aestronglyMeasurable
  have hufin : eLpNorm (u : V → ℝ) 2 (ν : Measure V) < ⊤ := (Lp.memLp u).2
  have hnorm_u : ∀ x, ‖(u : V → ℝ) x‖ ^ 2 = (u x) ^ 2 := fun x => by
    rw [Real.norm_eq_abs, sq_abs]
  obtain ⟨C₁, hC₁⟩ := (η.continuous.mul (η.continuous.mul
    hρc.continuous)).bounded_above_of_compact_support η.hasCompactSupport.mul_right
  have hwL : MemLp w 2 m := by
    refine ⟨hwm, lt_of_le_of_lt (eLpNorm_le_tilted_of_sq_le m hνU (C := max C₁ 0)
      (le_max_right _ _) u fun x => ?_) ?_⟩
    · have h1 : η x * (η x * FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x) ≤ max C₁ 0 :=
        (le_abs_self _).trans ((hC₁ x).trans (le_max_left _ _))
      have h2 : 0 ≤ FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x * ‖(u : V → ℝ) x‖ ^ 2 :=
        mul_nonneg (hρpos x).le (sq_nonneg _)
      calc ‖w x‖ ^ 2 = (η x * (η x * FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x)) *
            (FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x * ‖(u : V → ℝ) x‖ ^ 2) := by
            simp only [hw_def, hW_def, Real.norm_eq_abs, sq_abs]; ring
        _ ≤ max C₁ 0 * (FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x * ‖(u : V → ℝ) x‖ ^ 2) :=
            mul_le_mul_of_nonneg_right h1 h2
        _ = max C₁ 0 * FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x * ‖(u : V → ℝ) x‖ ^ 2 := by ring
    · exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        ENNReal.ofReal_ne_top) hufin
  obtain ⟨C₂, hC₂⟩ := ((η.continuous.mul (η.continuous.mul hρc.continuous)).mul
    (hUc.norm.pow 2)).bounded_above_of_compact_support (η.hasCompactSupport.mul_right.mul_right)
  have hGL : MemLp G 2 m := by
    refine ⟨hGm, lt_of_le_of_lt (eLpNorm_le_tilted_of_sq_le m hνU (C := max C₂ 0)
      (le_max_right _ _) u fun x => ?_) ?_⟩
    · have h1 : η x * (η x * FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x) * ‖gradient U x‖ ^ 2 ≤ max C₂ 0 :=
        (le_abs_self _).trans ((hC₂ x).trans (le_max_left _ _))
      have h2 : 0 ≤ FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x * ‖(u : V → ℝ) x‖ ^ 2 :=
        mul_nonneg (hρpos x).le (sq_nonneg _)
      calc ‖G x‖ ^ 2 = (η x * (η x * FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x) * ‖gradient U x‖ ^ 2) *
            (FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x * ‖(u : V → ℝ) x‖ ^ 2) := by
            simp only [hG_def, hW_def, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring
        _ ≤ max C₂ 0 * (FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x * ‖(u : V → ℝ) x‖ ^ 2) :=
            mul_le_mul_of_nonneg_right h1 h2
        _ = max C₂ 0 * FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x * ‖(u : V → ℝ) x‖ ^ 2 := by ring
    · exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        ENNReal.ofReal_ne_top) hufin
  have hwsupp : ∀ x ∉ closedBall (0 : V) (R + 2), w x = 0 := fun x hx => by
    simp only [hw_def, hηzero x hx, zero_mul]
  have hGsupp : ∀ x ∉ closedBall (0 : V) (R + 2), G x = 0 := fun x hx => by
    simp only [hG_def, hηzero x hx, zero_mul, zero_smul]
  have hwI : Integrable w m := memLp_one_iff_integrable.mp
    (hwL.mono_exponent_of_measure_support_ne_top hwsupp measure_closedBall_lt_top.ne one_le_two)
  have hGI : Integrable G m := memLp_one_iff_integrable.mp
    (hGL.mono_exponent_of_measure_support_ne_top hGsupp measure_closedBall_lt_top.ne one_le_two)
  -- the weak equation for `W`
  have hW : ∀ f : V → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      ∫ x, Laplacian.laplacian f x * W x ∂m =
        ∫ x, ⟪gradient f x, W x • gradient U x⟫ ∂m + ∫ x, f x * W x ∂m :=
    fun f hf hfc => hν.integral_laplacian_mul_tiltedDensity_mul_408915f m hi hνU hU u horth hf hfc
  -- the mollified sequence
  set v : ℕ → V → ℝ := fun n =>
    (FunctionalInequalities.KLS.LogConcave.mollifier (V := V) n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] w with hv_def
  set H : ℕ → V → V := fun n =>
    (FunctionalInequalities.KLS.LogConcave.mollifier (V := V) n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] G with hH_def
  have hvs : ∀ n, ContDiff ℝ ∞ (v n) := fun n =>
    HasCompactSupport.contDiff_convolution_left _
      ((FunctionalInequalities.KLS.LogConcave.mollifier (V := V) n).hasCompactSupport_normed (μ := m))
      (FunctionalInequalities.KLS.LogConcave.mollifier (V := V) n).contDiff_normed hwI.locallyIntegrable
  have hv1 : ∀ n, ContDiff ℝ 1 (v n) := fun n => (hvs n).of_le (WithTop.coe_le_coe.mpr le_top)
  have hvd : ∀ n, Differentiable ℝ (v n) := fun n => (hv1 n).differentiable one_ne_zero
  have hHc : ∀ n, Continuous (H n) := fun n => FunctionalInequalities.Analysis.Mollification.continuous_convolution _ hGI.locallyIntegrable
  have hvL : ∀ n, MemLp (v n) 2 m := fun n => FunctionalInequalities.Analysis.Mollification.memLp_convolution _ hwL
  have hHL : ∀ n, MemLp (H n) 2 m := fun n => FunctionalInequalities.Analysis.Mollification.memLp_convolution _ hGL
  have hvconv : Tendsto (fun n => eLpNorm (v n - w) 2 m) atTop (𝓝 0) :=
    FunctionalInequalities.Analysis.Mollification.tendsto_eLpNorm_convolution_sub_408915f tendsto_mollifier_rOut hwL
  have hHconv : Tendsto (fun n => eLpNorm (H n - G) 2 m) atTop (𝓝 0) :=
    FunctionalInequalities.Analysis.Mollification.tendsto_eLpNorm_convolution_sub_408915f tendsto_mollifier_rOut hGL
  -- the mollified weak equation, and its version for differences
  have hmoll : ∀ n (g : V → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ tsupport χ →
      ∫ x, Laplacian.laplacian g x * v n x ∂m =
        ∫ x, ⟪gradient g x, H n x⟫ ∂m + ∫ x, g x * v n x ∂m := fun n g hg hgc hgs =>
    FunctionalInequalities.KLS.LogConcave.integral_laplacian_mul_convolution_eq_408915f m hW η le_rfl hwI hGI (FunctionalInequalities.KLS.LogConcave.mollifier (V := V) n)
      (mollifier_rOut_le_one n) hg hgc (hgs.trans hR)
  have hdiff : ∀ n k (g : V → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ tsupport χ →
      ∫ x, Laplacian.laplacian g x * (v n - v k) x ∂m =
        ∫ x, ⟪gradient g x, (H n - H k) x⟫ ∂m + ∫ x, g x * (v n - v k) x ∂m := by
    intro n k g hg hgc hgs
    have hg1 : ContDiff ℝ 1 g := hg.of_le (WithTop.coe_le_coe.mpr le_top)
    have hg2 : ContDiff ℝ 2 g := hg.of_le (WithTop.coe_le_coe.mpr le_top)
    have i1 : ∀ j, Integrable (fun x => Laplacian.laplacian g x * v j x) m := fun j =>
      ((FunctionalInequalities.Analysis.BakryEmery.continuous_laplacian hg2).mul (hvs j).continuous).integrable_of_hasCompactSupport
        (FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_laplacian hgc).mul_right
    have i2 : ∀ j, Integrable (fun x => ⟪gradient g x, H j x⟫) m := fun j =>
      ((FunctionalInequalities.Analysis.BakryEmery.continuous_gradient hg1).inner (hHc j)).integrable_of_hasCompactSupport
        (hasCompactSupport_inner_left (FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_gradient hgc))
    have i3 : ∀ j, Integrable (fun x => g x * v j x) m := fun j =>
      (hg1.continuous.mul (hvs j).continuous).integrable_of_hasCompactSupport hgc.mul_right
    have h1 := hmoll n g hg hgc hgs
    have h2 := hmoll k g hg hgc hgs
    simp only [Pi.sub_apply, mul_sub, inner_sub_right]
    rw [integral_sub (i1 n) (i1 k), integral_sub (i2 n) (i2 k), integral_sub (i3 n) (i3 k)]
    linarith
  -- the Caccioppoli estimate for differences, in `eLpNorm` form
  have hcacc : ∀ n k, eLpNorm (fun x => χ x • gradient (v n - v k) x) 2 m ≤
      3 * eLpNorm (fun x => (v n - v k) x • gradient χ x) 2 m +
        2 * eLpNorm (fun x => χ x • (H n - H k) x) 2 m := by
    intro n k
    have hv' : ContDiff ℝ ∞ (v n - v k) := (hvs n).sub (hvs k)
    have hA : MemLp (fun x => χ x • gradient (v n - v k) x) 2 m :=
      (hχ.continuous.smul (FunctionalInequalities.Analysis.BakryEmery.continuous_gradient
        (hv'.of_le (WithTop.coe_le_coe.mpr le_top)))).memLp_of_hasCompactSupport hχc.smul_right
    have hB : MemLp (fun x => (v n - v k) x • gradient χ x) 2 m :=
      (hv'.continuous.smul (FunctionalInequalities.Analysis.BakryEmery.continuous_gradient hχ1)).memLp_of_hasCompactSupport
        (FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_gradient hχc).smul_left
    have hC : MemLp (fun x => χ x • (H n - H k) x) 2 m :=
      (hχ.continuous.smul ((hHc n).sub (hHc k))).memLp_of_hasCompactSupport hχc.smul_right
    have h := FunctionalInequalities.KLS.LogConcave.norm_toLp_smul_gradient_le_408915f m hχ hχc hv' (hdiff n k) hA hB hC
    rw [Lp.norm_toLp, Lp.norm_toLp, Lp.norm_toLp] at h
    have hA' := hA.eLpNorm_lt_top.ne
    have hB' := hB.eLpNorm_lt_top.ne
    have hC' := hC.eLpNorm_lt_top.ne
    rw [← ENNReal.ofReal_toReal hA', ← ENNReal.ofReal_toReal hB', ← ENNReal.ofReal_toReal hC']
    calc ENNReal.ofReal (eLpNorm (fun x => χ x • gradient (v n - v k) x) 2 m).toReal
        ≤ ENNReal.ofReal (3 * (eLpNorm (fun x => (v n - v k) x • gradient χ x) 2 m).toReal +
            2 * (eLpNorm (fun x => χ x • (H n - H k) x) 2 m).toReal) :=
          ENNReal.ofReal_le_ofReal h
      _ = _ := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
  -- the bounds on the cutoff and the density on the support of `χ`
  obtain ⟨M₁, hM₁⟩ := (FunctionalInequalities.Analysis.BakryEmery.continuous_gradient hχ1).bounded_above_of_compact_support
    (FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_gradient hχc)
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
  obtain ⟨M₂, hM₂⟩ := hχ.continuous.bounded_above_of_compact_support hχc
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ 0)
  obtain ⟨C₃, hC₃⟩ := (isCompact_closedBall (0 : V) R).exists_bound_of_continuousOn
    hρc.continuous.continuousOn
  obtain ⟨C₄, hC₄⟩ := (isCompact_closedBall (0 : V) R).exists_bound_of_continuousOn
    hρinvc.continuous.continuousOn
  have hC₄0 : 0 ≤ C₄ := (norm_nonneg _).trans (hC₄ 0 (mem_closedBall_self hR0.le))
  obtain ⟨M₅, hM₅⟩ := (hχ.continuous.mul hρinvc.continuous).bounded_above_of_compact_support
    hχc.mul_right
  have hM₅0 : 0 ≤ M₅ := (norm_nonneg _).trans (hM₅ 0)
  obtain ⟨M₆, hM₆⟩ := (hχ.continuous.smul (FunctionalInequalities.Analysis.BakryEmery.continuous_gradient
    hρinvc)).bounded_above_of_compact_support hχc.smul_right
  have hM₆0 : 0 ≤ M₆ := (norm_nonneg _).trans (hM₆ 0)
  have hρle : ∀ x ∈ tsupport χ, FunctionalInequalities.KLS.LogConcave.tiltedDensity m U x ≤ C₃ := fun x hx =>
    (le_abs_self _).trans (hC₃ x (hR hx))
  have hρinvle : ∀ x ∈ tsupport χ, ‖ρinv x‖ ≤ C₄ := fun x hx => hC₄ x (hR hx)
  have hgradχ : ∀ x ∉ tsupport χ, gradient χ x = 0 := fun x hx =>
    gradient_eq_zero_of_notMem_tsupport hx
  -- the tests `gₙ = χ vₙ / ρ`
  set gfun : ℕ → V → ℝ := fun n x => χ x * v n x * ρinv x with hgfun_def
  have hgc1 : ∀ n, ContDiff ℝ 1 (gfun n) := fun n => (hχ1.mul (hv1 n)).mul hρinvc
  have hgcs : ∀ n, HasCompactSupport (gfun n) := fun n => hχc.mul_right.mul_right
  have htest : ∀ n, FunctionalInequalities.Energy.WeightedGradient.IsTest ν (ContinuousLinearMap.id ℝ V) (gfun n) := fun n =>
    isTest_of_contDiff_one (hgc1 n) (hgcs n)
  have hmem : ∀ n, (htest n).memLp.toLp (gfun n) ∈
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain := fun n =>
    hν.toLp_mem_closedWeightedOperator_domain_of_isTest m _ hi (htest n)
  have hgradg : ∀ n x, gradient (gfun n) x = (χ x * v n x) • gradient ρinv x +
      ρinv x • (χ x • gradient (v n) x + v n x • gradient χ x) := by
    intro n x
    have h1 := FunctionalInequalities.Analysis.BakryEmery.gradient_mul (f := fun y => χ y * v n y) (g := ρinv) (x := x)
      ((hχd x).mul (hvd n x)) (hρinvd x)
    have h2 := FunctionalInequalities.Analysis.BakryEmery.gradient_mul (f := χ) (g := v n) (x := x) (hχd x) (hvd n x)
    refine h1.trans ?_
    rw [h2]
  have hgradsub : ∀ n k x, gradient (gfun n) x - gradient (gfun k) x =
      (χ x * (v n - v k) x) • gradient ρinv x + ρinv x • (χ x • gradient (v n - v k) x) +
        ρinv x • ((v n - v k) x • gradient χ x) := by
    intro n k x
    have hs : gradient (v n - v k) x = gradient (v n) x - gradient (v k) x :=
      FunctionalInequalities.Analysis.BakryEmery.gradient_sub (hvd n x) (hvd k x)
    rw [hgradg, hgradg, hs, Pi.sub_apply]
    module
  -- the sequence `T̄ [gₙ] = [∇gₙ]` and its Cauchy property
  have hY : ∀ n, hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hmem n⟩ =
      (htest n).memLp_apply.toLp (FunctionalInequalities.Energy.WeightedGradient.apply (ContinuousLinearMap.id ℝ V) (gfun n)) := fun n =>
    hν.closedWeightedOperator_apply_toLp m _ hi (htest n)
  have hdist : ∀ n k, dist (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
      ⟨_, hmem n⟩) (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hmem k⟩) =
      (eLpNorm (fun x => gradient (gfun n) x - gradient (gfun k) x) 2 (ν : Measure V)).toReal := by
    intro n k
    rw [hY, hY, Lp.dist_def]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [(htest n).memLp_apply.coeFn_toLp, (htest k).memLp_apply.coeFn_toLp]
      with x e1 e2
    rw [Pi.sub_apply, e1, e2, FunctionalInequalities.Energy.WeightedGradient.apply_id, FunctionalInequalities.Energy.WeightedGradient.apply_id]
  -- the three pieces of `∇gₙ - ∇gₖ`
  set K₀ : ℝ≥0∞ := ENNReal.ofReal C₃ ^ (1 / 2 : ℝ) with hK₀_def
  set K₁ : ℝ≥0∞ := ENNReal.ofReal M₆ + ENNReal.ofReal C₄ * (3 * ENNReal.ofReal M₁) +
    ENNReal.ofReal (C₄ * M₁) with hK₁_def
  set K₂ : ℝ≥0∞ := ENNReal.ofReal C₄ * (2 * ENNReal.ofReal M₂) with hK₂_def
  have hK₀ : K₀ ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hK₁ : K₁ ≠ ⊤ := by
    simp only [hK₁_def]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        ENNReal.ofReal_ne_top)⟩, ENNReal.ofReal_ne_top⟩
  have hK₂ : K₂ ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top)
  have hbound : ∀ n k, eLpNorm (fun x => gradient (gfun n) x - gradient (gfun k) x) 2
      (ν : Measure V) ≤ K₀ * (K₁ * eLpNorm (v n - v k) 2 m + K₂ * eLpNorm (H n - H k) 2 m) := by
    intro n k
    set d : V → ℝ := v n - v k with hd_def
    set Hd : V → V := H n - H k with hHd_def
    have hdc : Continuous d := ((hvs n).sub (hvs k)).continuous
    have hdgc : Continuous (gradient d) :=
      FunctionalInequalities.Analysis.BakryEmery.continuous_gradient (((hvs n).sub (hvs k)).of_le (WithTop.coe_le_coe.mpr le_top))
    have hHdc : Continuous Hd := (hHc n).sub (hHc k)
    set P₁ : V → V := fun x => (χ x * d x) • gradient ρinv x with hP₁_def
    set P₂ : V → V := fun x => ρinv x • (χ x • gradient d x) with hP₂_def
    set P₃ : V → V := fun x => ρinv x • (d x • gradient χ x) with hP₃_def
    have hP₁m : AEStronglyMeasurable P₁ m :=
      ((hχ.continuous.mul hdc).smul (FunctionalInequalities.Analysis.BakryEmery.continuous_gradient hρinvc)).aestronglyMeasurable
    have hP₂m : AEStronglyMeasurable P₂ m :=
      (hρinvc.continuous.smul (hχ.continuous.smul hdgc)).aestronglyMeasurable
    have hP₃m : AEStronglyMeasurable P₃ m :=
      (hρinvc.continuous.smul (hdc.smul (FunctionalInequalities.Analysis.BakryEmery.continuous_gradient hχ1))).aestronglyMeasurable
    have hsum : (fun x => gradient (gfun n) x - gradient (gfun k) x) = P₁ + P₂ + P₃ := by
      funext x
      simp only [Pi.add_apply, hP₁_def, hP₂_def, hP₃_def, hd_def]
      exact hgradsub n k x
    -- outside the support of `χ` all three pieces vanish
    have hzero : ∀ x ∉ tsupport χ, gradient (gfun n) x - gradient (gfun k) x = 0 := by
      intro x hx
      rw [hgradsub, image_eq_zero_of_notMem_tsupport hx, hgradχ x hx]
      simp
    -- the transfer to `ν`
    have hν_le : eLpNorm (fun x => gradient (gfun n) x - gradient (gfun k) x) 2 (ν : Measure V) ≤
        K₀ * eLpNorm (fun x => gradient (gfun n) x - gradient (gfun k) x) 2 m := by
      refine eLpNorm_tilted_le m hνU fun x hx => hρle x ?_
      by_contra hx'
      exact hx (hzero x hx')
    -- the three pieces in `L²(m)`
    have h₁ : eLpNorm P₁ 2 m ≤ ENNReal.ofReal M₆ * eLpNorm d 2 m := by
      refine eLpNorm_le_of_norm_le m hM₆0 fun x => ?_
      show ‖(χ x * d x) • gradient ρinv x‖ ≤ M₆ * ‖d x‖
      rw [mul_comm (χ x), mul_smul, norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hM₆ x) (norm_nonneg _)
    have h₂ : eLpNorm P₂ 2 m ≤ ENNReal.ofReal C₄ * eLpNorm (fun x => χ x • gradient d x) 2 m := by
      refine eLpNorm_le_of_norm_le m hC₄0 fun x => ?_
      simp only [hP₂_def]
      rw [norm_smul]
      by_cases hx : x ∈ tsupport χ
      · exact mul_le_mul_of_nonneg_right (hρinvle x hx) (norm_nonneg _)
      · rw [image_eq_zero_of_notMem_tsupport hx, zero_smul, norm_zero, mul_zero, mul_zero]
    have h₃ : eLpNorm P₃ 2 m ≤ ENNReal.ofReal (C₄ * M₁) * eLpNorm d 2 m := by
      refine eLpNorm_le_of_norm_le m (mul_nonneg hC₄0 hM₁0) fun x => ?_
      simp only [hP₃_def]
      rw [norm_smul, norm_smul]
      by_cases hx : x ∈ tsupport χ
      · calc ‖ρinv x‖ * (‖d x‖ * ‖gradient χ x‖) ≤ C₄ * (‖d x‖ * M₁) := by
              gcongr
              · exact hρinvle x hx
              · exact hM₁ x
          _ = C₄ * M₁ * ‖d x‖ := by ring
      · rw [hgradχ x hx, norm_zero, mul_zero, mul_zero]
        positivity
    have hBd : eLpNorm (fun x => d x • gradient χ x) 2 m ≤ ENNReal.ofReal M₁ * eLpNorm d 2 m := by
      refine eLpNorm_le_of_norm_le m hM₁0 fun x => ?_
      rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hM₁ x) (norm_nonneg _)
    have hCd : eLpNorm (fun x => χ x • Hd x) 2 m ≤ ENNReal.ofReal M₂ * eLpNorm Hd 2 m := by
      refine eLpNorm_le_of_norm_le m hM₂0 fun x => ?_
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hM₂ x) (norm_nonneg _)
    have hcac := hcacc n k
    calc eLpNorm (fun x => gradient (gfun n) x - gradient (gfun k) x) 2 (ν : Measure V)
        ≤ K₀ * eLpNorm (fun x => gradient (gfun n) x - gradient (gfun k) x) 2 m := hν_le
      _ ≤ K₀ * (eLpNorm P₁ 2 m + eLpNorm P₂ 2 m + eLpNorm P₃ 2 m) := by
          gcongr
          rw [hsum]
          exact (eLpNorm_add_le (hP₁m.add hP₂m) hP₃m one_le_two).trans
            (add_le_add_left (eLpNorm_add_le hP₁m hP₂m one_le_two) _)
      _ ≤ K₀ * (ENNReal.ofReal M₆ * eLpNorm d 2 m +
            ENNReal.ofReal C₄ * (3 * (ENNReal.ofReal M₁ * eLpNorm d 2 m) +
              2 * (ENNReal.ofReal M₂ * eLpNorm Hd 2 m)) +
            ENNReal.ofReal (C₄ * M₁) * eLpNorm d 2 m) := by
          gcongr
          refine h₂.trans ?_
          gcongr
          exact hcac.trans (by gcongr)
      _ = K₀ * (K₁ * eLpNorm d 2 m + K₂ * eLpNorm Hd 2 m) := by
          simp only [hK₁_def, hK₂_def]
          ring
  -- the bound tends to zero along `atTop` on pairs
  have hfst : Tendsto (fun p : ℕ × ℕ => p.1) atTop atTop := by
    rw [← Filter.prod_atTop_atTop_eq]; exact tendsto_fst
  have hsnd : Tendsto (fun p : ℕ × ℕ => p.2) atTop atTop := by
    rw [← Filter.prod_atTop_atTop_eq]; exact tendsto_snd
  have hvw : ∀ n, eLpNorm (v n - w) 2 m ≠ ⊤ := fun n => ((hvL n).sub hwL).eLpNorm_lt_top.ne
  have hHG : ∀ n, eLpNorm (H n - G) 2 m ≠ ⊤ := fun n => ((hHL n).sub hGL).eLpNorm_lt_top.ne
  set B : ℕ × ℕ → ℝ≥0∞ := fun p => K₀ * (K₁ * (eLpNorm (v p.1 - w) 2 m + eLpNorm (v p.2 - w) 2 m)
    + K₂ * (eLpNorm (H p.1 - G) 2 m + eLpNorm (H p.2 - G) 2 m)) with hB_def
  have hBfin : ∀ p, B p ≠ ⊤ := fun p =>
    ENNReal.mul_ne_top hK₀ (ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top hK₁ (ENNReal.add_ne_top.mpr ⟨hvw _, hvw _⟩),
        ENNReal.mul_ne_top hK₂ (ENNReal.add_ne_top.mpr ⟨hHG _, hHG _⟩)⟩)
  have hBlim : Tendsto B atTop (𝓝 0) := by
    have h1 : Tendsto (fun p : ℕ × ℕ => eLpNorm (v p.1 - w) 2 m + eLpNorm (v p.2 - w) 2 m) atTop
        (𝓝 (0 + 0)) := (hvconv.comp hfst).add (hvconv.comp hsnd)
    have h2 : Tendsto (fun p : ℕ × ℕ => eLpNorm (H p.1 - G) 2 m + eLpNorm (H p.2 - G) 2 m) atTop
        (𝓝 (0 + 0)) := (hHconv.comp hfst).add (hHconv.comp hsnd)
    rw [add_zero] at h1 h2
    have h3 := (ENNReal.Tendsto.const_mul h1 (Or.inr hK₁)).add
      (ENNReal.Tendsto.const_mul h2 (Or.inr hK₂))
    rw [mul_zero, mul_zero, add_zero] at h3
    have h4 := ENNReal.Tendsto.const_mul h3 (Or.inr hK₀)
    rw [mul_zero] at h4
    exact h4
  have hdist_le : ∀ p : ℕ × ℕ, dist (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
      ⟨_, hmem p.1⟩) (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hmem p.2⟩)
      ≤ (B p).toReal := by
    intro p
    rw [hdist]
    refine ENNReal.toReal_mono (hBfin p) ((hbound p.1 p.2).trans ?_)
    simp only [hB_def]
    gcongr
    · have : v p.1 - v p.2 = (v p.1 - w) - (v p.2 - w) := by abel
      rw [this]
      exact eLpNorm_sub_le ((hvL p.1).sub hwL).1 ((hvL p.2).sub hwL).1 one_le_two
    · have : H p.1 - H p.2 = (H p.1 - G) - (H p.2 - G) := by abel
      rw [this]
      exact eLpNorm_sub_le ((hHL p.1).sub hGL).1 ((hHL p.2).sub hGL).1 one_le_two
  have hcauchy : CauchySeq fun n =>
      hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hmem n⟩ := by
    rw [cauchySeq_iff_tendsto_dist_atTop_0]
    refine squeeze_zero (fun _ => dist_nonneg) hdist_le ?_
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hBlim
    rw [ENNReal.toReal_zero] at this
    exact this
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- convergence `[gₙ] → [χ u]` in `L²(ν)`
  have hgu : ∀ n x, gfun n x - χ x * u x = (χ x * ρinv x) * (v n - w) x := by
    intro n x
    by_cases hx : x ∈ tsupport χ
    · simp only [hgfun_def, hw_def, hW_def, Pi.sub_apply, hηχ x hx, one_mul]
      linear_combination (χ x * u x) * hρρinv x
    · simp [hgfun_def, image_eq_zero_of_notMem_tsupport hx]
  have hxa : Tendsto (fun n => (htest n).memLp.toLp (gfun n)) atTop
      (𝓝 ((FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _)) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    have heq : ∀ n, eLpNorm (((htest n).memLp.toLp (gfun n) : Lp ℝ 2 (ν : Measure V)) -
        ((FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _ :
          Lp ℝ 2 (ν : Measure V)) : V → ℝ) 2 (ν : Measure V) =
        eLpNorm (fun x => gfun n x - χ x * u x) 2 (ν : Measure V) := by
      intro n
      refine eLpNorm_congr_ae ?_
      filter_upwards [(htest n).memLp.coeFn_toLp,
        (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).coeFn_toLp] with x e1 e2
      rw [Pi.sub_apply, e1, e2]
    simp only [heq]
    have hle : ∀ n, eLpNorm (fun x => gfun n x - χ x * u x) 2 (ν : Measure V) ≤
        K₀ * (ENNReal.ofReal M₅ * eLpNorm (v n - w) 2 m) := by
      intro n
      have hzero : ∀ x ∉ tsupport χ, gfun n x - χ x * u x = 0 := fun x hx => by
        rw [hgu, image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
      refine (eLpNorm_tilted_le m hνU fun x hx => hρle x ?_).trans ?_
      · by_contra hx'
        exact hx (hzero x hx')
      · gcongr
        refine eLpNorm_le_of_norm_le m hM₅0 fun x => ?_
        rw [hgu, norm_mul]
        exact mul_le_mul_of_nonneg_right (hM₅ x) (norm_nonneg _)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun n => bot_le) hle
    have h := ENNReal.Tendsto.const_mul (a := K₀) (ENNReal.Tendsto.const_mul
      (a := ENNReal.ofReal M₅) hvconv (Or.inr ENNReal.ofReal_ne_top)) (Or.inr hK₀)
    rwa [mul_zero, mul_zero] at h
  obtain ⟨hmem', -⟩ := FunctionalInequalities.Analysis.Semigroup.exists_mem_domain_apply_eq_of_tendsto
    (hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi) hmem hxa hb
  exact hmem'
