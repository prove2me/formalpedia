-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.PoissonIterate.symmetrize_taylorField_grad0_step_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:54:10.552976+00:00
-- url     : https://prove2.me/submissions/453fad68-21f5-4411-ac9c-f0ebac01a2dd

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
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_PoissonIterate_Taylor
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
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_taylorTensor_const_mul_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_symmetrize_apply_comp_cast_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_taylorTensor_center_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_taylorTensor_gen_apply_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_existsUnique_centered_adjointComp_eq_408915f

section
noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff ENNReal
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
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section Lp
section ScalarLp
omit [CompleteSpace E] [FiniteDimensional ℝ E]
section NormedSpace
variable {G : Type*}
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
section CompleteSpace
variable [CompleteSpace G]
omit [BorelSpace E] in
/-- Tilt averages only see the `μ`-class of a function: every tilt `μ_z` is absolutely
continuous with respect to `μ`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.tiltAverage_congr_ae (μ : Measure E) {f g : E → G} (hfg : f =ᵐ[μ] g) (z : E) :
    tiltAverage μ f z = tiltAverage μ g z := by
  unfold tiltAverage expTilt
  exact integral_congr_ae ((tilted_absolutelyContinuous μ _).ae_le hfg)
omit [BorelSpace E] in
/-- Taylor tensors only see the `μ`-class of a function. -/
theorem FunctionalInequalities.Analysis.BakryEmery.taylorTensor_congr_ae (μ : Measure E) {f g : E → G} (hfg : f =ᵐ[μ] g) (d : ℕ) :
    taylorTensor μ f d = taylorTensor μ g d := by
  unfold taylorTensor
  rw [show tiltAverage μ f = tiltAverage μ g from funext (tiltAverage_congr_ae μ hfg)]
end CompleteSpace
end NormedSpace
end ScalarLp
end Lp
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
/-- The mean preserves subtraction. -/
@[simp]
theorem FunctionalInequalities.L2.mean_sub (μ : ProbabilityMeasure α) (f g : Lp ℝ 2 (μ : Measure α)) :
    mean μ (f - g) = mean μ f - mean μ g := by
  rw [mean, inner_sub_left]
  rfl
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
/-- The total generator agrees with `T†T` on its domain. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen_of_mem {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (adjointComp T).domain) :
    gen T u = adjointComp T ⟨u, hu⟩ :=
  dif_pos hu
/-- The total generator is homogeneous on the domain of `T†T`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen_smul (c : ℝ) {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (adjointComp T).domain) :
    gen T (c • u) = c • gen T u := by
  rw [gen_of_mem T ((adjointComp T).domain.smul_mem c hu), gen_of_mem T hu]
  exact LinearPMap.map_smul (adjointComp T) c ⟨u, hu⟩
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
/-- The components of one step lie in `D(A)`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.step_mem_domain {k : ℕ} (h : Field ν k) (J : Fin (k + 1) → Fin (Module.finrank ℝ V)) :
    step T̄ h J ∈ (adjointComp T̄).domain :=
  (adjointComp T̄).domain.smul_mem _
    (centeredInv_mem_domain m hν hi hνU hU hC (mean_grad0 (T̄) h J))
include hνU hU hC in
/-- **BKL (30)** for one step: `-L (α (-L)⁻¹ ∇₀h) = α ∇₀h`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.genField_step {k : ℕ} (h : Field ν k) :
    genField T̄ (step T̄ h) = scale T̄ h • grad0 T̄ h := by
  funext J
  rw [genField, step, Pi.smul_apply, Pi.smul_apply, invField,
    gen_smul _ _ (centeredInv_mem_domain m hν hi hνU hU hC (mean_grad0 (T̄) h J)),
    gen_centeredInv m hν hi hνU hU hC (mean_grad0 (T̄) h J)]
end HeatModel
end
end
end
end
end
end

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
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
section Generic
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : ProbabilityMeasure V}
omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- `T_d` is homogeneous on `L²(ν)` classes. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorTensor_Lp_smul (c : ℝ) (u : Lp ℝ 2 (ν : Measure V)) (d : ℕ) :
    taylorTensor (ν : Measure V) (⇑(c • u)) d = c • taylorTensor (ν : Measure V) (⇑u) d := by
  rw [taylorTensor_congr_ae _ (Lp.coeFn_smul c u) d]
  exact taylorTensor_const_mul_408915f _ c _ d
end Generic
section Slots
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.append_cast_natAdd {α : Type*} {d k : ℕ} (h : d + (k + 2) = d + 1 + (k + 1))
    (a : Fin (d + 1) → α) (I : Fin (k + 1) → α) :
    (fun p : Fin (k + 2) => Fin.append a I (Fin.cast h (Fin.natAdd d p))) =
      Fin.cons (a (Fin.last d)) I := by
  funext p
  induction p using Fin.cases with
  | zero =>
    rw [show Fin.cast h (Fin.natAdd d 0) = Fin.castAdd (k + 1) (Fin.last d) from Fin.ext (by simp),
      Fin.append_left, Fin.cons_zero]
  | succ p =>
    rw [show Fin.cast h (Fin.natAdd d p.succ) = Fin.natAdd (d + 1) p from
      Fin.ext (by simp; omega), Fin.append_right, Fin.cons_succ]
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.append_cast_castAdd {α : Type*} {d k : ℕ} (h : d + (k + 2) = d + 1 + (k + 1))
    (a : Fin (d + 1) → α) (I : Fin (k + 1) → α) (p : Fin d) :
    Fin.append a I (Fin.cast h (Fin.castAdd (k + 2) p)) = a (Fin.castSucc p) := by
  rw [show Fin.cast h (Fin.castAdd (k + 2) p) = Fin.castAdd (k + 1) (Fin.castSucc p) from
    Fin.ext (by simp), Fin.append_left]
end Slots
section HeatModel
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
  (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
variable {C : NNReal} (hC : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate
end FunctionalInequalities.KLS.LogConcave.PoissonIterate
open FunctionalInequalities.KLS.LogConcave.PoissonIterate in
include hνU hU hexp hC in
/-- **BKL Corollary 3.7 for one step**: for `d ≥ 1` and `h' = α (-L)⁻¹∇₀h`,
`S_{d+1} T_d(∇₀h') = α T_{d+1}(∇₀h)`, the index positions of the two coefficient arrays identified
by `Fin.cast`. -/
theorem solution {k : ℕ} (h : FunctionalInequalities.KLS.LogConcave.PoissonIterate.Field ν k) {d : ℕ} (hd : 1 ≤ d)
    (J : Fin (d + 1 + (k + 1)) → Fin (Module.finrank ℝ V)) :
    FunctionalInequalities.Analysis.Tensor.symmetrize (Module.finrank ℝ V) (d + (k + 2)) (d + 1)
        (FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField d (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h))) (J ∘ Fin.cast (by omega)) =
      FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ h * FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField (d + 1) (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ h) J := by
  rw [FunctionalInequalities.KLS.LogConcave.PoissonIterate.symmetrize_apply_comp_cast_408915f]
  set I : Fin (k + 1) → Fin (Module.finrank ℝ V) := J ∘ Fin.natAdd (d + 1)
  set i : Fin (d + 1) → Fin (Module.finrank ℝ V) := J ∘ Fin.castAdd (k + 1)
  have hgen : FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h I) = FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ h • FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ h I :=
    congrFun (FunctionalInequalities.KLS.LogConcave.PoissonIterate.genField_step m hν hi hνU hU hC h) I
  have hR : FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ h * FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField (d + 1) (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ h) J =
      FunctionalInequalities.Analysis.BakryEmery.taylorTensor (ν : Measure V) (⇑(FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h I))) (d + 1)
        (fun p => stdOrthonormalBasis ℝ V (i p)) := by
    rw [hgen, FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorTensor_Lp_smul]
    rfl
  rw [hR, FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorTensor_gen_apply_408915f m hν hi hνU hU hexp (FunctionalInequalities.KLS.LogConcave.PoissonIterate.step_mem_domain m hν hi hνU hU hC h I)]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorField, PiLp.toLp_apply, Function.comp_apply]
  rw [append_cast_natAdd, FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0, FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField, Fin.cons_zero, Fin.tail_cons,
    FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorTensor_center_408915f hexp _ hd]
  simp only [append_cast_castAdd, Function.comp_apply]
  rfl
