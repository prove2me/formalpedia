-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.tiltAverage_adjointComp_eq_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:46:49.323762+00:00
-- url     : https://prove2.me/submissions/552f5dba-dc7c-4b4e-ac26-418a75e2423b

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
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_expTilt_of_memLp_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_tiltAverage_neg_weightedLaplacian_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_Semigroup_tendsto_apply_of_tendsto_adjointComp_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_seq_smooth_tendsto_adjointComp_of_localRegularity_408915f
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal_408915f

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
end CompleteSpace
end NormedSpace
/-- The tilt average of a class `g ∈ L²(μ)` at `z` is `(∫ e^{⟪z, x⟫} dμ)⁻¹ ⟪e^{⟪z, ·⟫}, g⟫`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.tiltAverage_Lp_eq_inner (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (g : Lp ℝ 2 μ) (z : E) :
    tiltAverage μ (⇑g) z =
      (∫ x, Real.exp ⟪z, x⟫ ∂μ)⁻¹ * ⟪(memLp_exp_inner μ hexp z).toLp _, g⟫ := by
  rw [tiltAverage, expTilt, integral_tilted, L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [(memLp_exp_inner μ hexp z).coeFn_toLp] with x hx
  rw [hx, smul_eq_mul, RCLike.inner_apply, conj_trivial, div_eq_mul_inv]
  ring
/-- For fixed `z`, `g ↦ F_g(z)` is continuous on `L²(μ)`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.continuous_tiltAverage_Lp (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (z : E) :
    Continuous fun g : Lp ℝ 2 μ => tiltAverage μ (⇑g) z := by
  simp_rw [tiltAverage_Lp_eq_inner μ hexp _ z]
  exact continuous_const.mul (continuous_const.inner continuous_id)
end ScalarLp
omit [FiniteDimensional ℝ E] in
/-- Pairing the tilt average of a vector class `G ∈ L²(μ; E)` with `w` is the tilt average of the
scalar class `⟪w, G⟫`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.inner_tiltAverage_Lp (μ : Measure E) [IsFiniteMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (G : Lp E 2 μ) (w z : E) :
    ⟪w, tiltAverage μ (⇑G) z⟫ = tiltAverage μ (⇑((innerSL ℝ w).compLpL 2 μ G)) z := by
  rw [tiltAverage_congr_ae μ ((innerSL ℝ w).coeFn_compLpL G) z]
  unfold tiltAverage
  simp only [innerSL_apply_apply]
  exact (integral_inner (integrable_expTilt_of_memLp_408915f μ hexp (Lp.memLp G) z) w).symm
end Lp
end
end
end
end
end

section
noncomputable section
open MeasureTheory FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff LinearPMap RealInnerProductSpace
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
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section Generator
variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
include hνU hU in
/-- **the smooth-test generator identity, value clause**: for `f ∈ C_c^∞(V)`, `T̄†T̄ [f] = [-ℒ f]` with `ℒ f = Δ f - ⟪∇U, ∇f⟫`.
The generator of the heat semigroup `P_t = exp (-t T̄†T̄)` is therefore `ℒ` on smooth compactly
supported tests: `d/dt P_t f |_{t=0} = ℒ f`. -/
theorem FunctionalInequalities.KLS.LogConcave.adjointComp_toLp_eq {f : V → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
        ⟨(memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f,
          hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ =
      (memLp_neg_weightedLaplacian (ν := ν) hU hf hfc).toLp (fun x => -weightedLaplacian U f x) := by
  rw [adjointComp_apply]
  refine LinearPMap.adjoint_apply_eq
    (hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) _ fun x => ?_
  rw [hν.inner_toLp_neg_weightedLaplacian_eq m hi hνU hU hf hfc x]
  congr 1
  exact (hν.closedWeightedOperator_toLp_eq m hi hf hfc).symm
end Generator
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology Metric InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
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
section Tilted
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}
variable (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)
/-- **`C_c^∞(V)` is an operator core of the generator `A = T̄†T̄`.** For `ν = m.tilted (-U)` with
a `C¹` potential and unit weight, every `F ∈ D(A)` is the limit of smooth compactly supported
classes in the graph norm of `A`: there are `fₙ ∈ C_c^∞(V)` with `[fₙ] → F` and `A [fₙ] → A F` in
`L²(ν)`. Equivalently, `ℒ = Δ - ⟪∇U, ∇·⟫` is essentially self-adjoint on `C_c^∞(V)` in `L²(ν)`.

This is the operator-core criterion `exists_seq_smooth_tendsto_adjointComp_of_localRegularity`
with its hypothesis discharged by `toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal`; it
is exactly the hypothesis `hcore` of `HeatSemigroup.integral_mul_weakGamma_apply_nonneg_of_core`.
No convexity of `U`, no semigroup and no `Γ₂` input is used. -/
theorem FunctionalInequalities.KLS.LogConcave.exists_seq_smooth_tendsto_adjointComp
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    (F : ((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain) :
    ∃ (fn : ℕ → V → ℝ) (hfn : ∀ n, ContDiff ℝ ∞ (fn n))
      (hfnc : ∀ n, HasCompactSupport (fn n)),
      Tendsto (fun n => ‖(memLp_of_contDiff_hasCompactSupport ν (hfn n) (hfnc n)).toLp (fn n)
        - (F : (Lp ℝ 2 (ν : Measure V)))‖) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖((adjointComp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n)
          (hfnc n)⟩ : (Lp ℝ 2 (ν : Measure V))) - ((adjointComp
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) F : (Lp ℝ 2
              (ν : Measure V)))‖) atTop (𝓝 0) :=
  hν.exists_seq_smooth_tendsto_adjointComp_of_localRegularity_408915f m hi hνU hU
    (fun u horth _χ hχ hχc =>
      hν.toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal_408915f m hi hνU hU u horth hχ hχc) F
end Tilted
end
end
end
end
end

noncomputable section
open MeasureTheory Filter Topology
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped ContDiff RealInnerProductSpace ENNReal
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
section Generator
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
/-- (48) for smooth compactly supported classes, read on the `L²` classes `A [f] = [-ℒf]` and
`T̄ [f] = [∇f]`. -/
private theorem FunctionalInequalities.KLS.LogConcave.tiltAverage_adjointComp_toLp_eq (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ 1 U) {f : V → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (z : V) :
    tiltAverage (ν : Measure V)
        (⇑(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩)) z =
      ⟪z, tiltAverage (ν : Measure V)
        (⇑(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩)) z⟫ := by
  rw [hν.adjointComp_toLp_eq m hi hνU hU hf hfc, hν.closedWeightedOperator_toLp_eq m hi hf hfc,
    tiltAverage_congr_ae _ (MemLp.coeFn_toLp _) z,
    tiltAverage_congr_ae _ (MemLp.coeFn_toLp _) z, hνU]
  exact tiltAverage_neg_weightedLaplacian_408915f m hU (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hfc z
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave in
/-- **BKL (48) on the generator domain**: for `ν = m.tilted (-U)` with `U ∈ C¹` and all
exponential moments, and `F ∈ D(A)`, `F_{A F}(z) = ⟪z, F_{T̄ F}(z)⟫` for every `z`. -/
theorem solution (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ 1 U)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    (F : (FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (z : V) :
    FunctionalInequalities.Analysis.BakryEmery.tiltAverage (ν : Measure V)
        (⇑(FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F)) z =
      ⟪z, FunctionalInequalities.Analysis.BakryEmery.tiltAverage (ν : Measure V)
        (⇑(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)) z⟫ := by
  obtain ⟨fn, hfn, hfnc, h0, h1⟩ := hν.exists_seq_smooth_tendsto_adjointComp m hi hνU hU F
  let x : ℕ → (FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain :=
    fun n => ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n) (hfnc n)⟩
  have hx0 : Tendsto (fun n => (x n : Lp ℝ 2 (ν : Measure V))) atTop
      (𝓝 (F : Lp ℝ 2 (ν : Measure V))) := tendsto_iff_norm_sub_tendsto_zero.2 h0
  have hx1 : Tendsto
      (fun n => FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (x n))
      atTop (𝓝 (FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F)) :=
    tendsto_iff_norm_sub_tendsto_zero.2 h1
  have hT := FunctionalInequalities.Analysis.Semigroup.tendsto_apply_of_tendsto_adjointComp_408915f
    (hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) hx0 hx1
  have hL := ((FunctionalInequalities.Analysis.BakryEmery.continuous_tiltAverage_Lp (ν : Measure V) hexp z).tendsto _).comp hx1
  have hR := (((FunctionalInequalities.Analysis.BakryEmery.continuous_tiltAverage_Lp (ν : Measure V) hexp z).comp
    ((innerSL ℝ z).compLpL 2 (ν : Measure V)).continuous).tendsto _).comp hT
  rw [FunctionalInequalities.Analysis.BakryEmery.inner_tiltAverage_Lp (ν : Measure V) hexp]
  refine tendsto_nhds_unique hL (hR.congr fun n => ?_)
  simp only [Function.comp_apply]
  rw [← FunctionalInequalities.Analysis.BakryEmery.inner_tiltAverage_Lp (ν : Measure V) hexp]
  exact (tiltAverage_adjointComp_toLp_eq m hν hi hνU hU (hfn n) (hfnc n) z).symm
