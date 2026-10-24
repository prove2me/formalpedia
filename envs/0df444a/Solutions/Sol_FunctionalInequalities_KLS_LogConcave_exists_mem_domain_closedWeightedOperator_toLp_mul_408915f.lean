-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.exists_mem_domain_closedWeightedOperator_toLp_mul_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:31:59.126381+00:00
-- url     : https://prove2.me/submissions/f2526b6f-5ffd-495e-b1ed-1cfd4217c774

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
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Measurable
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
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.PiL2
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
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_seq_smooth_tendsto_graph_408915f

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
open MeasureTheory Filter InnerProductSpace
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
namespace FunctionalInequalities.Energy.WeightedGradient
end FunctionalInequalities.Energy.WeightedGradient
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient
open Energy.Euclidean FunctionalInequalities.Analysis.BakryEmery
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} {B : V →L[ℝ] V} {m : Measure V} [m.IsAddHaarMeasure]
variable {g₁ g₂ g : V → ℝ}
omit [SecondCountableTopology V] in
/-- **Leibniz rule for the weighted gradient**, `ν`-almost everywhere:
`B ∇(g₁ g₂) = g₁ (B ∇g₂) + g₂ (B ∇g₁)`. Only absolute continuity and the two Lipschitz
witnesses are used; no boundedness and no `L²` membership. -/
theorem FunctionalInequalities.Energy.WeightedGradient.IsTest.apply_mul_ae (hac : (ν : Measure V) ≪ m)
    (h₁ : IsTest ν B g₁) (h₂ : IsTest ν B g₂) :
    apply B (fun x => g₁ x * g₂ x) =ᵐ[(ν : Measure V)]
      fun x => g₁ x • apply B g₂ x + g₂ x • apply B g₁ x := by
  obtain ⟨K₁, hK₁⟩ := h₁.1
  obtain ⟨K₂, hK₂⟩ := h₂.1
  filter_upwards [hac.ae_le (LipschitzApproximation.ae_differentiableAt_of_locallyLipschitz
      hK₁.locallyLipschitz m),
    hac.ae_le (LipschitzApproximation.ae_differentiableAt_of_locallyLipschitz
      hK₂.locallyLipschitz m)] with x hx₁ hx₂
  simp only [apply, gradient_mul hx₁ hx₂, map_add, map_smul]
end
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.L2
end FunctionalInequalities.L2
open FunctionalInequalities FunctionalInequalities.L2
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
section BddSmul
variable {c : α → ℝ} {M : ℝ}
theorem FunctionalInequalities.L2.coeFn_bddSmulL (hc : AEStronglyMeasurable c μ) (hM : ∀ᵐ x ∂μ, |c x| ≤ M)
    (u : Lp H 2 μ) :
    (bddSmulL hc hM u : α → H) =ᵐ[μ] fun x => c x • (u x) :=
  coeFn_bddSmulₗ hc hM u
end BddSmul
section BddSmulRight
variable {β : α → H} {M : ℝ}
theorem FunctionalInequalities.L2.coeFn_bddSmulRightL (hβ : AEStronglyMeasurable β μ) (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M)
    (u : Lp ℝ 2 μ) :
    (bddSmulRightL hβ hM u : α → H) =ᵐ[μ] fun x => (u x) • β x :=
  coeFn_bddSmulRightₗ hβ hM u
end BddSmulRight
end
end
end
end

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
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
open Energy Energy.WeightedGradient FunctionalInequalities.Analysis.Semigroup
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section Multiplier
variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave in
/-- **Leibniz rule for the closed weighted gradient against a smooth compactly supported
multiplier.** For `φ ∈ C_c^∞(V)` and **every** `x ∈ D(T̄)` the class of `φ x` lies in `D(T̄)`, and

`T̄ (φ x) = φ (T̄ x) + x (B ∇φ)`  almost everywhere.

The proof approximates `x` in the graph norm by smooth compactly supported `gₙ`
(`exists_seq_smooth_tendsto_graph`), applies the classical product rule to `φ gₙ`, and passes to
the limit: both `φ` and `B ∇φ` are bounded, so multiplication by either is a bounded operator on
`L²`, and closedness of `T̄` identifies the limit. No boundedness or differentiability of `x` is
used. -/
theorem solution {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (x : (hν.closedWeightedOperator m B hi).domain) :
    ∃ hmem : (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hφ hφc
        (x : Lp ℝ 2 (ν : Measure V))).toLp _ ∈ (hν.closedWeightedOperator m B hi).domain,
      ((hν.closedWeightedOperator m B hi ⟨_, hmem⟩ : Lp V 2 (ν : Measure V)) : V → V)
        =ᵐ[(ν : Measure V)] fun y =>
          φ y • ((hν.closedWeightedOperator m B hi x : Lp V 2 (ν : Measure V)) : V → V) y
            + (x : Lp ℝ 2 (ν : Measure V)) y • FunctionalInequalities.Energy.WeightedGradient.apply B φ y := by
  classical
  have hac : (ν : Measure V) ≪ m := hν.absolutelyContinuous_haar m hi
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (mod_cast le_top)
  have hβcont : Continuous (FunctionalInequalities.Energy.WeightedGradient.apply B φ) :=
    B.continuous.comp (FunctionalInequalities.Analysis.BakryEmery.continuous_gradient hφ1)
  obtain ⟨M, hM⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  obtain ⟨N, hN⟩ := hβcont.bounded_above_of_compact_support (FunctionalInequalities.Energy.WeightedGradient.hasCompactSupport_apply B hφc)
  have hMb : ∀ᵐ y ∂(ν : Measure V), |φ y| ≤ M :=
    Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hM y
  have hNb : ∀ᵐ y ∂(ν : Measure V), ‖FunctionalInequalities.Energy.WeightedGradient.apply B φ y‖ ≤ N := Filter.Eventually.of_forall hN
  set cm := FunctionalInequalities.L2.bddSmulL (H := ℝ) hφ.continuous.aestronglyMeasurable hMb with hcm
  set cv := FunctionalInequalities.L2.bddSmulL (H := V) hφ.continuous.aestronglyMeasurable hMb with hcv
  set cr := FunctionalInequalities.L2.bddSmulRightL (H := V) hβcont.aestronglyMeasurable hNb with hcr
  obtain ⟨g, hg, hgc, h1, h2⟩ := hν.exists_seq_smooth_tendsto_graph_408915f m B hi x
  -- the smooth products and their membership
  have hprod : ∀ n, ContDiff ℝ ∞ fun y => φ y * g n y := fun n => hφ.mul (hg n)
  have hprodc : ∀ n, HasCompactSupport fun y => φ y * g n y := fun n => hφc.mul_right
  have htest : ∀ n, FunctionalInequalities.Energy.WeightedGradient.IsTest ν B fun y => φ y * g n y := fun n =>
    FunctionalInequalities.Energy.WeightedGradient.IsTest.of_contDiff_hasCompactSupport ν B (hprod n) (hprodc n)
  have hdom : ∀ n, (FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hprod n) (hprodc n)).toLp
      (fun y => φ y * g n y) ∈ (hν.closedWeightedOperator m B hi).domain := fun n =>
    hν.toLp_mem_closedWeightedOperator_domain_of_isTest m B hi (htest n)
  -- the first convergence
  have e1 : ∀ n, (FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hprod n) (hprodc n)).toLp
      (fun y => φ y * g n y)
      = cm ((FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp (g n)) := by
    intro n
    refine Lp.ext ?_
    filter_upwards [(FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hprod n) (hprodc n)).coeFn_toLp,
      FunctionalInequalities.L2.coeFn_bddSmulL (H := ℝ) hφ.continuous.aestronglyMeasurable hMb
        ((FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp (g n)),
      (FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).coeFn_toLp] with y hy1 hy2 hy3
    rw [hy1, hcm, hy2, hy3, smul_eq_mul]
  have e0 : (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hφ hφc
      (x : Lp ℝ 2 (ν : Measure V))).toLp _ = cm (x : Lp ℝ 2 (ν : Measure V)) := by
    refine Lp.ext ?_
    filter_upwards [(FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hφ hφc
        (x : Lp ℝ 2 (ν : Measure V))).coeFn_toLp,
      FunctionalInequalities.L2.coeFn_bddSmulL (H := ℝ) hφ.continuous.aestronglyMeasurable hMb
        (x : Lp ℝ 2 (ν : Measure V))] with y hy1 hy2
    rw [hy1, hcm, hy2, smul_eq_mul]
  have hconv1 : Tendsto (fun n => (FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hprod n)
      (hprodc n)).toLp (fun y => φ y * g n y)) atTop
      (𝓝 ((FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hφ hφc
        (x : Lp ℝ 2 (ν : Measure V))).toLp _)) := by
    rw [e0]
    exact ((cm.continuous.tendsto _).comp h1).congr fun n => (e1 n).symm
  -- the second convergence
  have e2 : ∀ n, hν.closedWeightedOperator m B hi ⟨_, hdom n⟩
      = cv ((FunctionalInequalities.Energy.WeightedGradient.IsTest.of_contDiff_hasCompactSupport ν B (hg n)
          (hgc n)).memLp_apply.toLp (FunctionalInequalities.Energy.WeightedGradient.apply B (g n)))
        + cr ((FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp (g n)) := by
    intro n
    have hrep := hν.closedWeightedOperator_apply_toLp m B hi (htest n)
    have hsub : (⟨_, hdom n⟩ : (hν.closedWeightedOperator m B hi).domain)
        = ⟨(htest n).memLp.toLp _, hν.toLp_mem_closedWeightedOperator_domain_of_isTest m B hi
            (htest n)⟩ := rfl
    rw [hsub, hrep]
    refine Lp.ext ?_
    filter_upwards [(htest n).memLp_apply.coeFn_toLp,
      Lp.coeFn_add (cv ((FunctionalInequalities.Energy.WeightedGradient.IsTest.of_contDiff_hasCompactSupport ν B (hg n)
          (hgc n)).memLp_apply.toLp (FunctionalInequalities.Energy.WeightedGradient.apply B (g n))))
        (cr ((FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp (g n))),
      FunctionalInequalities.L2.coeFn_bddSmulL (H := V) hφ.continuous.aestronglyMeasurable hMb
        ((FunctionalInequalities.Energy.WeightedGradient.IsTest.of_contDiff_hasCompactSupport ν B (hg n) (hgc n)).memLp_apply.toLp
          (FunctionalInequalities.Energy.WeightedGradient.apply B (g n))),
      FunctionalInequalities.L2.coeFn_bddSmulRightL (H := V) hβcont.aestronglyMeasurable hNb
        ((FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp (g n)),
      (FunctionalInequalities.Energy.WeightedGradient.IsTest.of_contDiff_hasCompactSupport ν B (hg n) (hgc n)).memLp_apply.coeFn_toLp,
      (FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).coeFn_toLp,
      FunctionalInequalities.Energy.WeightedGradient.IsTest.apply_mul_ae (m := m) hac (FunctionalInequalities.Energy.WeightedGradient.IsTest.of_contDiff_hasCompactSupport ν B hφ hφc)
        (FunctionalInequalities.Energy.WeightedGradient.IsTest.of_contDiff_hasCompactSupport ν B (hg n) (hgc n))] with
      y hy1 hy2 hy3 hy4 hy5 hy6 hy7
    rw [hy1, hy2, Pi.add_apply, hcv, hy3, hcr, hy4, hy5, hy6, hy7]
  have hconv2 : Tendsto (fun n => hν.closedWeightedOperator m B hi ⟨_, hdom n⟩) atTop
      (𝓝 (cv (hν.closedWeightedOperator m B hi x) + cr (x : Lp ℝ 2 (ν : Measure V)))) := by
    refine Tendsto.congr (fun n => (e2 n).symm) ?_
    exact (((cv.continuous.tendsto _).comp h2).add ((cr.continuous.tendsto _).comp h1))
  obtain ⟨hmem, heq⟩ := FunctionalInequalities.Analysis.Semigroup.exists_mem_domain_apply_eq_of_tendsto
    (hν.closedWeightedOperator_isClosed m B hi) hdom hconv1 hconv2
  refine ⟨hmem, ?_⟩
  rw [heq]
  filter_upwards [Lp.coeFn_add (cv (hν.closedWeightedOperator m B hi x))
      (cr (x : Lp ℝ 2 (ν : Measure V))),
    FunctionalInequalities.L2.coeFn_bddSmulL (H := V) hφ.continuous.aestronglyMeasurable hMb
      (hν.closedWeightedOperator m B hi x),
    FunctionalInequalities.L2.coeFn_bddSmulRightL (H := V) hβcont.aestronglyMeasurable hNb
      (x : Lp ℝ 2 (ν : Measure V))] with y hy1 hy2 hy3
  rw [hy1, Pi.add_apply, hcv, hy2, hcr, hy3]
