-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.norm_center_sq_sub_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T18:01:35.674069+00:00
-- url     : https://prove2.me/submissions/4efe685a-4fac-4dec-81c3-a3bb80de48e0

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
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
import Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_Generated_norm_sq_sub_norm_apply_sq_le_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_closedWeightedOperator_center_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_closedWeightedOperator_one_eq_zero_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_mul_norm_closedWeightedOperator_sq_le_408915f

section
noncomputable section
open Filter InnerProductSpace MeasureTheory Topology
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
namespace FunctionalInequalities.Analysis.Semigroup
end FunctionalInequalities.Analysis.Semigroup
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Semigroup
section
namespace FunctionalInequalities.Analysis.Semigroup.LpMarkov
end FunctionalInequalities.Analysis.Semigroup.LpMarkov
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.Semigroup.LpMarkov
variable {α H : Type*} [MeasurableSpace α]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (μ : ProbabilityMeasure α)
variable {μ : ProbabilityMeasure α} {T : Lp ℝ 2 (μ : Measure α) →ₗ.[ℝ] H}
/-- If one lies in the form domain and has zero energy, every resolvent fixes it. -/
theorem FunctionalInequalities.Analysis.Semigroup.LpMarkov.resolventCLM_one (hT : T.IsClosed) {s : ℝ} (hs : 0 < s)
    (hone : L2.const μ 1 ∈ T.domain) (hTone : T ⟨L2.const μ 1, hone⟩ = 0) :
    resolventCLM T hT hs (L2.const μ 1) = L2.const μ 1 := by
  let oneDom : T.domain := ⟨L2.const μ 1, hone⟩
  have hweak : WeakResolvent T s (L2.const μ 1) oneDom := by
    intro v
    change ⟪L2.const μ 1, (v : Lp ℝ 2 (μ : Measure α))⟫ + s * ⟪T oneDom, T v⟫ = _
    rw [hTone, inner_zero_left, mul_zero, add_zero]
  rw [resolventCLM_apply, ← eq_resolventDomain T hT hs hweak]
omit [CompleteSpace H] in
/-- Exponentiating an operator that kills `f` fixes `f`. -/
theorem FunctionalInequalities.Analysis.Semigroup.LpMarkov.exp_apply_of_apply_eq_zero
    (A : Lp ℝ 2 (μ : Measure α) →L[ℝ] Lp ℝ 2 (μ : Measure α))
    (f : Lp ℝ 2 (μ : Measure α)) (hAf : A f = 0) : NormedSpace.exp A f = f := by
  have hsum := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A).mapL
    (ContinuousLinearMap.apply ℝ (Lp ℝ 2 (μ : Measure α)) f)
  apply hsum.unique
  convert hasSum_ite_eq 0 f using 1
  ext n
  rcases n with _ | n
  · simp
  · simp [pow_succ, hAf]
/-- If the resolvent fixes one, its Yosida approximation kills one. -/
theorem FunctionalInequalities.Analysis.Semigroup.LpMarkov.yosida_one (hT : T.IsClosed) {s : ℝ} (hs : 0 < s)
    (hone : L2.const μ 1 ∈ T.domain) (hTone : T ⟨L2.const μ 1, hone⟩ = 0) :
    yosida T hT hs (L2.const μ 1) = 0 := by
  rw [yosida_apply, resolventCLM_one hT hs hone hTone, sub_self, smul_zero]
/-- Every Yosida exponential fixes one. -/
theorem FunctionalInequalities.Analysis.Semigroup.LpMarkov.exp_neg_smul_yosida_one (hT : T.IsClosed) {s : ℝ} (hs : 0 < s) (t : ℝ)
    (hone : L2.const μ 1 ∈ T.domain) (hTone : T ⟨L2.const μ 1, hone⟩ = 0) :
    NormedSpace.exp (-t • yosida T hT hs) (L2.const μ 1) = L2.const μ 1 := by
  apply exp_apply_of_apply_eq_zero
  change -t • yosida T hT hs (L2.const μ 1) = 0
  rw [yosida_one hT hs hone hTone, smul_zero]
end
section
namespace FunctionalInequalities.Analysis.Semigroup.Generated
end FunctionalInequalities.Analysis.Semigroup.Generated
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.Semigroup.Generated
open LpMarkov
variable {α H : Type*} [MeasurableSpace α]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : ProbabilityMeasure α} {T : Lp ℝ 2 (μ : Measure α) →ₗ.[ℝ] H}
/-- If the form kills one, the generated semigroup fixes one. -/
theorem FunctionalInequalities.Analysis.Semigroup.Generated.one (hT : T.IsClosed) (hd : Dense (T.domain : Set (Lp ℝ 2
    (μ : Measure α)))) {t : ℝ} (ht : 0 ≤ t)
    (hone : L2.const μ 1 ∈ T.domain) (hTone : T ⟨L2.const μ 1, hone⟩ = 0) :
    Generated.apply T hT hd t (L2.const μ 1) = L2.const μ 1 := by
  refine (Generated.eq_apply_of_tendsto T hT hd ht (L2.const μ 1) (L2.const μ 1) ?_).symm
  intro ε hε
  refine ⟨1, one_pos, ?_⟩
  intro s hs _
  rw [exp_neg_smul_yosida_one hT hs t hone hTone, sub_self, norm_zero]
  exact hε
/-- Symmetry and preservation of one imply preservation of the `L²` mean. -/
theorem FunctionalInequalities.Analysis.Semigroup.Generated.mean (hT : T.IsClosed) (hd : Dense (T.domain : Set (Lp ℝ 2
    (μ : Measure α)))) {t : ℝ} (ht : 0 ≤ t)
    (hone : L2.const μ 1 ∈ T.domain) (hTone : T ⟨L2.const μ 1, hone⟩ = 0)
    (f : Lp ℝ 2 (μ : Measure α)) :
    L2.mean μ (Generated.apply T hT hd t f) = L2.mean μ f := by
  rw [L2.mean, Generated.symmetric T hT hd ht,
    Generated.one hT hd ht hone hTone]
  rfl
end
end
end
end
end
end

section
noncomputable section
open Filter InnerProductSpace MeasureTheory Topology
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
open Energy Energy.Euclidean
open FunctionalInequalities.Analysis.Semigroup
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
section
namespace FunctionalInequalities.KLS.LogConcave.HeatSemigroup
end FunctionalInequalities.KLS.LogConcave.HeatSemigroup
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.HeatSemigroup
/-- The heat semigroup fixes the constant one. -/
theorem FunctionalInequalities.KLS.LogConcave.HeatSemigroup.one (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {t : ℝ} (ht : 0 ≤ t) :
    HeatSemigroup.operator m B hν hi ht (L2.const ν 1) = L2.const ν 1 := by
  exact FunctionalInequalities.Analysis.Semigroup.Generated.one
    (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) ht
    (one_mem_domain_closedWeightedOperator m B hν hi)
    (closedWeightedOperator_one_eq_zero_408915f m B hν hi)
/-- The heat semigroup preserves the `L²` mean. -/
theorem FunctionalInequalities.KLS.LogConcave.HeatSemigroup.mean (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {t : ℝ} (ht : 0 ≤ t)
    (f : Lp ℝ 2 (ν : Measure V)) :
    L2.mean ν (HeatSemigroup.operator m B hν hi ht f) = L2.mean ν f := by
  exact FunctionalInequalities.Analysis.Semigroup.Generated.mean
    (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) ht
    (one_mem_domain_closedWeightedOperator m B hν hi)
    (closedWeightedOperator_one_eq_zero_408915f m B hν hi) f
end
end
end
end
end
end

section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set InnerProductSpace
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
namespace FunctionalInequalities.KLS.LogConcave.HeatSemigroup
end FunctionalInequalities.KLS.LogConcave.HeatSemigroup
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.HeatSemigroup
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)
/-- The actual heat operator fixes every L2 constant. -/
theorem FunctionalInequalities.KLS.LogConcave.HeatSemigroup.const_fixed {t : ℝ} (ht : 0 ≤ t) (c : ℝ) :
    operator m B hν hi ht (L2.const ν c) = L2.const ν c := by
  have hc : L2.const ν c = c • L2.const ν 1 := by
    simpa using L2.const_smul ν c 1
  rw [hc, map_smul]
  simp only [one m B hν hi ht]
/-- Centering commutes with the actual heat operator. -/
theorem FunctionalInequalities.KLS.LogConcave.HeatSemigroup.center_operator {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 (ν : Measure V)) :
    L2.center ν (operator m B hν hi ht f) =
      operator m B hν hi ht (L2.center ν f) := by
  rw [L2.center, L2.center, HeatSemigroup.mean m B hν hi ht f, map_sub,
    const_fixed m B hν hi ht]
end
end
end
end
end
end

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
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
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave in
include hνU hU in
/-- The finite-time Poincaré bound: if `∇∇U ≥ ρ > 0`, then for `u ∈ D(T̄)` and `t ≥ 0`,
`Var(u) - Var(P_t u) ≤ (1 - e^{-2ρt}) / ρ · ‖T̄ u‖²`. -/
theorem solution {ρ : ℝ} (hρ : 0 < ρ)
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    (u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖FunctionalInequalities.L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 -
        ‖FunctionalInequalities.L2.center ν
          (FunctionalInequalities.KLS.LogConcave.HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht u)‖ ^ 2 ≤
      (1 - Real.exp (-2 * ρ * t)) / ρ *
        ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u‖ ^ 2 := by
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let hT := hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
  let hd := hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi

  let c : T.domain :=
    ⟨FunctionalInequalities.L2.center ν (u : Lp ℝ 2 (ν : Measure V)),
      FunctionalInequalities.KLS.LogConcave.center_mem_closedWeightedOperator_domain m hν hi u⟩

  have hcurv :
      ∀ y : (FunctionalInequalities.Analysis.Semigroup.adjointComp T).domain,
        ρ * ‖T ⟨y, y.2.2⟩‖ ^ 2 ≤ ‖FunctionalInequalities.Analysis.Semigroup.adjointComp T y‖ ^ 2 := by
    intro y
    exact FunctionalInequalities.KLS.LogConcave.mul_norm_closedWeightedOperator_sq_le_408915f m hν hi hνU hU hH y

  have hkey :=
    FunctionalInequalities.Analysis.Semigroup.Generated.norm_sq_sub_norm_apply_sq_le_408915f T hT hd hρ hcurv c ht

  have hcenter :
      FunctionalInequalities.L2.center ν
          (FunctionalInequalities.KLS.LogConcave.HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht
            (u : Lp ℝ 2 (ν : Measure V))) =
        FunctionalInequalities.KLS.LogConcave.HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht
          (FunctionalInequalities.L2.center ν (u : Lp ℝ 2 (ν : Measure V))) := by
    exact FunctionalInequalities.KLS.LogConcave.HeatSemigroup.center_operator m (ContinuousLinearMap.id ℝ V) hν hi ht
      (u : Lp ℝ 2 (ν : Measure V))

  rw [hcenter]

  change
    ‖(c : Lp ℝ 2 (ν : Measure V))‖ ^ 2 -
        ‖FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t c‖ ^ 2 ≤
      (1 - Real.exp (-2 * ρ * t)) / ρ *
        ‖T u‖ ^ 2

  have hTc :
      T c = T u := by
    simpa [c, T] using
      (FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_center_408915f m hν hi u)

  rw [hTc] at hkey
  exact hkey
