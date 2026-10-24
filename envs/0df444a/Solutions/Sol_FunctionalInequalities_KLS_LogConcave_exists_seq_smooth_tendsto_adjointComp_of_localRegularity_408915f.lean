-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.exists_seq_smooth_tendsto_adjointComp_of_localRegularity_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:38:03.287615+00:00
-- url     : https://prove2.me/submissions/35d9cad1-afb4-481e-a3a8-9fb9c1c911dc

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
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_eq_zero_of_localRegularity_408915f

noncomputable section
open MeasureTheory Filter Topology Metric Set InnerProductSpace
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
open Energy Energy.WeightedGradient
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section Criterion
variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave in
/-- **Operator-core criterion: local regularity of deficiency elements implies that `C_c^∞(V)`
is an operator core of `A = T̄†T̄`.**

Assume that every `u ∈ L²(ν)` orthogonal to `(A + 1) C_c^∞(V)` has all of its localizations
`[χ u]`, `χ ∈ C_c^∞(V)`, in the form domain `D(T̄)`. Then every `F ∈ D(A)` is the limit of smooth
compactly supported classes **in the graph norm of `A`**: `[fₙ] → F` and `A [fₙ] → A F` in
`L²(ν)`. This is the hypothesis `hcore` of
`HeatSemigroup.integral_mul_weakGamma_apply_nonneg_of_core`.

The proof is the standard deficiency argument: `eq_zero_of_localRegularity` says that the
orthogonal complement of the range of `A + 1` on `C_c^∞(V)` is trivial, so that range is dense;
and `‖(A + 1) v‖² = ‖A v‖² + 2 ‖T̄ v‖² + ‖v‖²` converts approximation of `(A + 1) F` into
simultaneous approximation of `F` and `A F`. Nothing beyond the stated hypothesis is assumed: the
potential is only `C¹` and no convexity, no semigroup and no `Γ₂` input is used. -/
theorem solution
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    (hreg : ∀ u : (Lp ℝ 2 (ν : Measure V)),
      (∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
        ⟪((FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ : (Lp ℝ 2 (ν : Measure V))), u⟫ +
          ⟪((FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f : (Lp ℝ 2
            (ν : Measure V))), u⟫ = 0) →
      ∀ (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ),
        (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _ ∈
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    (F : ((FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain) :
    ∃ (fn : ℕ → V → ℝ) (hfn : ∀ n, ContDiff ℝ ∞ (fn n))
      (hfnc : ∀ n, HasCompactSupport (fn n)),
      Tendsto (fun n => ‖(FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν (hfn n) (hfnc n)).toLp (fn n)
        - (F : (Lp ℝ 2 (ν : Measure V)))‖) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖((FunctionalInequalities.Analysis.Semigroup.adjointComp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n)
          (hfnc n)⟩ : (Lp ℝ 2 (ν : Measure V))) - ((FunctionalInequalities.Analysis.Semigroup.adjointComp
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) F : (Lp ℝ 2
              (ν : Measure V)))‖) atTop (𝓝 0) := by
  classical
  have hd : Dense (((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain : Set
    (Lp ℝ 2 (ν : Measure V))) :=
    hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  set Ψ : ((FunctionalInequalities.Analysis.Semigroup.adjointComp
    (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain →ₗ[ℝ] (Lp ℝ 2
      (ν : Measure V)) := ((FunctionalInequalities.Analysis.Semigroup.adjointComp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).toFun + ((FunctionalInequalities.Analysis.Semigroup.adjointComp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain.subtype with hΨ
  have hΨapply : ∀ v : ((FunctionalInequalities.Analysis.Semigroup.adjointComp
    (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain, Ψ v = ((FunctionalInequalities.Analysis.Semigroup.adjointComp
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) v : (Lp ℝ 2
        (ν : Measure V))) + (v : (Lp ℝ 2 (ν : Measure V))) := fun v => rfl
  set K : Submodule ℝ (Lp ℝ 2 (ν : Measure V)) :=
    Submodule.map Ψ (Submodule.comap ((FunctionalInequalities.Analysis.Semigroup.adjointComp
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain.subtype (FunctionalInequalities.Energy.WeightedGradient.smoothCore ν)) with hK
  -- the orthogonal complement of the range is trivial
  have hKorth : Kᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro u hu
    have horth : ∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
        ⟪((FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ : (Lp ℝ 2 (ν : Measure V))), u⟫ +
          ⟪((FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f : (Lp ℝ 2
            (ν : Measure V))), u⟫ = 0 := by
      intro f hf hfc
      have hmemK : Ψ ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ ∈ K :=
        Submodule.mem_map_of_mem ⟨f, hf, hfc, rfl⟩
      have h0 := (Submodule.mem_orthogonal K u).mp hu _ hmemK
      rw [hΨapply, inner_add_left] at h0
      exact h0
    exact FunctionalInequalities.KLS.LogConcave.eq_zero_of_localRegularity_408915f m hν hi hνU hU u horth (hreg u horth)
  have hdense : Dense (K : Set (Lp ℝ 2 (ν : Measure V))) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (Submodule.topologicalClosure_eq_top_iff.mpr hKorth)
  obtain ⟨x, hxK, hxlim⟩ := mem_closure_iff_seq_limit.mp (hdense (Ψ F))
  have hchoice : ∀ n, ∃ z : ((FunctionalInequalities.Analysis.Semigroup.adjointComp
    (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain, (z : (Lp ℝ 2
      (ν : Measure V))) ∈ FunctionalInequalities.Energy.WeightedGradient.smoothCore ν ∧ Ψ z = x n := by
    intro n
    obtain ⟨z, hzmem, hzeq⟩ := hxK n
    exact ⟨z, hzmem, hzeq⟩
  choose z hzs hzeq using hchoice
  have hzsm : ∀ n, ∃ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
      (z n : (Lp ℝ 2 (ν : Measure V))) =
        (FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f := hzs
  choose fn hfn hfnc hfneq using hzsm
  -- the graph-norm comparison
  have hcmp : ∀ n, ‖(z n : (Lp ℝ 2 (ν : Measure V))) - (F : (Lp ℝ 2
    (ν : Measure V)))‖ ≤ ‖x n - Ψ F‖ ∧
      ‖((FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) (z n) :
        (Lp ℝ 2 (ν : Measure V))) - ((FunctionalInequalities.Analysis.Semigroup.adjointComp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) F : (Lp ℝ 2
            (ν : Measure V)))‖ ≤ ‖x n - Ψ F‖ := by
    intro n
    have hv : Ψ (z n - F) = x n - Ψ F := by rw [map_sub, hzeq n]
    have hcoe : ((z n - F : ((FunctionalInequalities.Analysis.Semigroup.adjointComp
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain) : (Lp ℝ 2
        (ν : Measure V))) = (z n : (Lp ℝ 2 (ν : Measure V))) - (F : (Lp ℝ 2 (ν : Measure V))) := rfl
    have hAsub : ((FunctionalInequalities.Analysis.Semigroup.adjointComp
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) (z n - F) : (Lp ℝ 2
        (ν : Measure V))) = ((FunctionalInequalities.Analysis.Semigroup.adjointComp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) (z n) : (Lp ℝ 2
            (ν : Measure V))) - ((FunctionalInequalities.Analysis.Semigroup.adjointComp
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) F : (Lp ℝ 2
                (ν : Measure V))) :=
      LinearPMap.map_sub _ _ _
    have hnn : 0 ≤ ⟪((FunctionalInequalities.Analysis.Semigroup.adjointComp
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) (z n - F) : (Lp ℝ 2
        (ν : Measure V))), ((z n - F : ((FunctionalInequalities.Analysis.Semigroup.adjointComp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain) : (Lp ℝ 2
            (ν : Measure V)))⟫ := by
      rw [FunctionalInequalities.Analysis.Semigroup.inner_adjointComp_self hd (z n - F)]
      positivity
    have hexp : ‖Ψ (z n - F)‖ ^ 2 = ‖((FunctionalInequalities.Analysis.Semigroup.adjointComp
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) (z n - F) : (Lp ℝ 2
        (ν : Measure V)))‖ ^ 2 +
        2 * ⟪((FunctionalInequalities.Analysis.Semigroup.adjointComp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) (z n - F) : (Lp ℝ 2
            (ν : Measure V))), ((z n - F : ((FunctionalInequalities.Analysis.Semigroup.adjointComp
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain) : (Lp ℝ 2
                (ν : Measure V)))⟫ +
        ‖((z n - F : ((FunctionalInequalities.Analysis.Semigroup.adjointComp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain) : (Lp ℝ 2
            (ν : Measure V)))‖ ^ 2 := by
      rw [hΨapply]
      exact norm_add_sq_real _ _
    rw [hAsub, hcoe] at hnn
    rw [hv, hcoe, hAsub] at hexp
    constructor
    · nlinarith [hexp, hnn, norm_nonneg (x n - Ψ F), norm_nonneg ((z n : (Lp ℝ 2
      (ν : Measure V))) - (F : (Lp ℝ 2 (ν : Measure V)))),
        norm_nonneg (((FunctionalInequalities.Analysis.Semigroup.adjointComp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) (z n) : (Lp ℝ 2
            (ν : Measure V))) - ((FunctionalInequalities.Analysis.Semigroup.adjointComp
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) F : (Lp ℝ 2
                (ν : Measure V))))]
    · nlinarith [hexp, hnn, norm_nonneg (x n - Ψ F), norm_nonneg ((z n : (Lp ℝ 2
      (ν : Measure V))) - (F : (Lp ℝ 2 (ν : Measure V)))),
        norm_nonneg (((FunctionalInequalities.Analysis.Semigroup.adjointComp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) (z n) : (Lp ℝ 2
            (ν : Measure V))) - ((FunctionalInequalities.Analysis.Semigroup.adjointComp
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) F : (Lp ℝ 2
                (ν : Measure V))))]
  have hlim0 : Tendsto (fun n => ‖x n - Ψ F‖) atTop (𝓝 0) := by
    have := (hxlim.sub (tendsto_const_nhds (x := Ψ F))).norm
    simpa using this
  have hzeq' : ∀ n, (⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n)
      (hfnc n)⟩ : ((FunctionalInequalities.Analysis.Semigroup.adjointComp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain) = z n := fun n => Subtype.ext (hfneq n).symm
  refine ⟨fn, hfn, hfnc, ?_, ?_⟩
  · refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim0
    rw [← hfneq n]
    exact (hcmp n).1
  · refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim0
    rw [hzeq' n]
    exact (hcmp n).2
