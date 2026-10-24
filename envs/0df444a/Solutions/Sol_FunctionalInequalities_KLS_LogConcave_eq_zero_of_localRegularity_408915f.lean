-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.eq_zero_of_localRegularity_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:36:16.318047+00:00
-- url     : https://prove2.me/submissions/b430aca0-028b-43ce-937f-c1518ff5f93b

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
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_norm_toLp_mul_cutoff_le_408915f

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
section Cutoff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
private theorem FunctionalInequalities.KLS.LogConcave.cutoff_nonneg (r : ℝ) (y : V) : 0 ≤ FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r y :=
  (FunctionalInequalities.KLS.LogConcave.profile (V := V)).nonneg
private theorem FunctionalInequalities.KLS.LogConcave.cutoff_le_one (r : ℝ) (y : V) : FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r y ≤ 1 :=
  (FunctionalInequalities.KLS.LogConcave.profile (V := V)).le_one
private theorem FunctionalInequalities.KLS.LogConcave.cutoff_eq_one {r : ℝ} (hr : 0 < r) {y : V} (hy : ‖y‖ ≤ 5 * r) :
    FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r y = 1 := by
  apply (FunctionalInequalities.KLS.LogConcave.profile (V := V)).one_of_mem_closedBall
  rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr),
    ← div_eq_inv_mul, div_le_iff₀ hr]
  exact hy
/-- A single bound for the gradients of the whole scaled family. -/
private theorem FunctionalInequalities.KLS.LogConcave.exists_norm_gradient_cutoff_le :
    ∃ M : ℝ, 0 < M ∧ ∀ r : ℝ, 0 < r → ∀ y : V, ‖gradient (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r) y‖ ≤ M / r := by
  have hb : ContDiff ℝ 1 ((FunctionalInequalities.KLS.LogConcave.profile (V := V)) : V → ℝ) := (FunctionalInequalities.KLS.LogConcave.profile (V := V)).contDiff
  obtain ⟨M, hM⟩ := ((FunctionalInequalities.KLS.LogConcave.profile (V := V)).hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hb.continuous_fderiv one_ne_zero)
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun r hr y => ?_⟩
  have hlin : HasFDerivAt (fun y : V => r⁻¹ • y) (r⁻¹ • ContinuousLinearMap.id ℝ V) y :=
    (hasFDerivAt_id y).const_smul _
  have hd := (hb.differentiable one_ne_zero _).hasFDerivAt.comp y hlin
  have hnorm : ‖gradient (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r) y‖ = ‖fderiv ℝ (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r) y‖ := by
    rw [gradient, (toDual ℝ V).symm.norm_map]
  rw [hnorm]
  have hfd : fderiv ℝ (FunctionalInequalities.KLS.LogConcave.cutoff (V := V) r) y
      = fderiv ℝ (((FunctionalInequalities.KLS.LogConcave.profile (V := V)) : V → ℝ) ∘ fun y : V => r⁻¹ • y) y := rfl
  rw [hfd, hd.fderiv]
  have hop : ‖r⁻¹ • ContinuousLinearMap.id ℝ V‖ ≤ r⁻¹ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr)]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (inv_nonneg.2 hr.le)).trans_eq
      (mul_one _)
  calc
    _ ≤ ‖fderiv ℝ ((FunctionalInequalities.KLS.LogConcave.profile (V := V)) : V → ℝ) (r⁻¹ • y)‖ *
        ‖r⁻¹ • ContinuousLinearMap.id ℝ V‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ max M 1 * r⁻¹ := mul_le_mul ((hM _).trans (le_max_left _ _)) hop
      (norm_nonneg _) (le_trans zero_le_one (le_max_right _ _))
    _ = max M 1 / r := (div_eq_mul_inv _ _).symm
end Cutoff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section Criterion
variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave in
/-- **A deficiency element of the minimal generator that is locally in the form domain
vanishes.**

Let `u ∈ L²(ν)` be orthogonal to `(A + 1) C_c^∞(V)`, that is, `⟪A [f], u⟫ + ⟪[f], u⟫ = 0` for
every smooth compactly supported `f`. If every localization `[χ u]`, `χ ∈ C_c^∞(V)`, lies in the
form domain `D(T̄)`, then `u = 0`.

Only *local* membership is assumed: no global gradient of `u`, no smoothness of `u` and no
classical representative are used. The passage from local to global is the cutoff estimate
`‖χ_r u‖ ≤ (M / r) ‖u‖`, which is where completeness of the ambient Euclidean space enters. The
potential is only `C¹` and no convexity is used. -/
theorem solution
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U) (u : (Lp ℝ 2 (ν : Measure V)))
    (horth : ∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
      ⟪((FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ : (Lp ℝ 2 (ν : Measure V))), u⟫ +
        ⟪((FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f : (Lp ℝ 2 (ν : Measure V))), u⟫ = 0)
    (hloc : ∀ (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ),
      (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _ ∈
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    u = 0 := by
  classical
  obtain ⟨M, hM0, hM⟩ := exists_norm_gradient_cutoff_le (V := V)
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hbound : ∀ n : ℕ, ‖(FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
      (FunctionalInequalities.KLS.LogConcave.contDiff_cutoff ((n : ℝ) + 1)) (FunctionalInequalities.KLS.LogConcave.hasCompactSupport_cutoff (hpos n)) u).toLp _‖
      ≤ M / ((n : ℝ) + 1) * ‖u‖ := fun n =>
    FunctionalInequalities.KLS.LogConcave.norm_toLp_mul_cutoff_le_408915f m hν hi hνU hU u horth hloc (hpos n) hM0.le (hM _ (hpos n))
  -- the localizations converge to `u` in `L²`, by dominated convergence
  have hsq : ∀ n : ℕ, ‖u - (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
      (FunctionalInequalities.KLS.LogConcave.contDiff_cutoff ((n : ℝ) + 1)) (FunctionalInequalities.KLS.LogConcave.hasCompactSupport_cutoff (hpos n)) u).toLp _‖ ^ 2
      = ∫ y, ((1 - FunctionalInequalities.KLS.LogConcave.cutoff (V := V) ((n : ℝ) + 1) y) * u y) ^ 2 ∂(ν : Measure V) := by
    intro n
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub u ((FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
        (FunctionalInequalities.KLS.LogConcave.contDiff_cutoff ((n : ℝ) + 1)) (FunctionalInequalities.KLS.LogConcave.hasCompactSupport_cutoff (hpos n)) u).toLp _),
      (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
        (FunctionalInequalities.KLS.LogConcave.contDiff_cutoff ((n : ℝ) + 1)) (FunctionalInequalities.KLS.LogConcave.hasCompactSupport_cutoff (hpos n)) u).coeFn_toLp] with
      y e1 e2
    rw [Real.inner_apply, e1, Pi.sub_apply, e2]
    ring
  have hdom : Tendsto
    (fun n : ℕ => ∫ y, ((1 - FunctionalInequalities.KLS.LogConcave.cutoff (V := V) ((n : ℝ) + 1) y) * u y) ^ 2 ∂(ν : Measure V))
      atTop (𝓝 0) := by
    have hint : Integrable (fun y => (u y) ^ 2) (ν : Measure V) := (Lp.memLp u).integrable_sq
    have hmeas : ∀ n : ℕ, AEStronglyMeasurable
        (fun y => ((1 - FunctionalInequalities.KLS.LogConcave.cutoff (V := V) ((n : ℝ) + 1) y) * u y) ^ 2) (ν : Measure V) := by
      intro n
      exact ((((continuous_const.sub
        (FunctionalInequalities.KLS.LogConcave.contDiff_cutoff ((n : ℝ) + 1)).continuous)).aestronglyMeasurable).mul
          (Lp.aestronglyMeasurable u)).pow 2
    have hbd : ∀ n : ℕ, ∀ᵐ y ∂(ν : Measure V),
        ‖((1 - FunctionalInequalities.KLS.LogConcave.cutoff (V := V) ((n : ℝ) + 1) y) * u y) ^ 2‖ ≤ (u y) ^ 2 := by
      intro n
      refine Filter.Eventually.of_forall fun y => ?_
      have h1 : |1 - FunctionalInequalities.KLS.LogConcave.cutoff (V := V) ((n : ℝ) + 1) y| ≤ 1 :=
        abs_le.mpr ⟨by linarith [cutoff_le_one ((n : ℝ) + 1) y], by
          linarith [cutoff_nonneg ((n : ℝ) + 1) y]⟩
      have h2 : ((1 - FunctionalInequalities.KLS.LogConcave.cutoff (V := V) ((n : ℝ) + 1) y) * u y) ^ 2 ≤ (u y) ^ 2 := by
        have := mul_le_mul_of_nonneg_right h1 (abs_nonneg (u y))
        calc ((1 - FunctionalInequalities.KLS.LogConcave.cutoff (V := V) ((n : ℝ) + 1) y) * u y) ^ 2
            = (|1 - FunctionalInequalities.KLS.LogConcave.cutoff (V := V) ((n : ℝ) + 1) y| * |u y|) ^ 2 := by
              rw [← abs_mul, sq_abs]
          _ ≤ (1 * |u y|) ^ 2 := by
              apply pow_le_pow_left₀ (by positivity) this
          _ = (u y) ^ 2 := by rw [one_mul, sq_abs]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact h2
    have hlim : ∀ᵐ y ∂(ν : Measure V), Tendsto
        (fun n : ℕ => ((1 - FunctionalInequalities.KLS.LogConcave.cutoff (V := V) ((n : ℝ) + 1) y) * u y) ^ 2) atTop (𝓝 0) := by
      refine Filter.Eventually.of_forall fun y => ?_
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      refine (Filter.eventually_atTop.2 ⟨⌈‖y‖⌉₊, fun n hn => ?_⟩)
      have hy : ‖y‖ ≤ 5 * ((n : ℝ) + 1) := by
        have h1 : ‖y‖ ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
        linarith
      simp [cutoff_eq_one (hpos n) hy]
    have := tendsto_integral_of_dominated_convergence (μ := (ν : Measure V))
      (F := fun (n : ℕ) y => ((1 - FunctionalInequalities.KLS.LogConcave.cutoff (V := V) ((n : ℝ) + 1) y) * u y) ^ 2)
      (f := fun _ : V => (0 : ℝ)) (fun y => (u y) ^ 2) hmeas hint hbd hlim
    simpa using this
  have hten : Tendsto (fun n : ℕ => ‖u - (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
      (FunctionalInequalities.KLS.LogConcave.contDiff_cutoff ((n : ℝ) + 1)) (FunctionalInequalities.KLS.LogConcave.hasCompactSupport_cutoff (hpos n)) u).toLp _‖)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ‖u - (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
        (FunctionalInequalities.KLS.LogConcave.contDiff_cutoff ((n : ℝ) + 1)) (FunctionalInequalities.KLS.LogConcave.hasCompactSupport_cutoff (hpos n)) u).toLp _‖ ^ 2)
        atTop (𝓝 0) := by
      simpa only [hsq] using hdom
    have h2 := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h1
    simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at h2
    exact h2
  -- the two bounds force `‖u‖ = 0`
  have hzero : ‖u‖ ≤ 0 := by
    have hsum : Tendsto (fun n : ℕ => ‖u - (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
        (FunctionalInequalities.KLS.LogConcave.contDiff_cutoff ((n : ℝ) + 1)) (FunctionalInequalities.KLS.LogConcave.hasCompactSupport_cutoff (hpos n)) u).toLp _‖
        + M / ((n : ℝ) + 1) * ‖u‖) atTop (𝓝 0) := by
      have h3 : Tendsto (fun n : ℕ => M / ((n : ℝ) + 1) * ‖u‖) atTop (𝓝 0) := by
        have := (tendsto_const_div_atTop_nhds_zero_nat M).mul_const ‖u‖
        simpa using (tendsto_const_nhds.div_atTop
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)).mul_const ‖u‖
      simpa using hten.add h3
    refine ge_of_tendsto hsum (Filter.Eventually.of_forall fun n => ?_)
    calc ‖u‖ = ‖(u - (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
          (FunctionalInequalities.KLS.LogConcave.contDiff_cutoff ((n : ℝ) + 1)) (FunctionalInequalities.KLS.LogConcave.hasCompactSupport_cutoff (hpos n)) u).toLp _)
          + (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
          (FunctionalInequalities.KLS.LogConcave.contDiff_cutoff ((n : ℝ) + 1)) (FunctionalInequalities.KLS.LogConcave.hasCompactSupport_cutoff (hpos n)) u).toLp _‖ := by
            rw [sub_add_cancel]
      _ ≤ ‖u - (FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
          (FunctionalInequalities.KLS.LogConcave.contDiff_cutoff ((n : ℝ) + 1)) (FunctionalInequalities.KLS.LogConcave.hasCompactSupport_cutoff (hpos n)) u).toLp _‖
          + ‖(FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν)
          (FunctionalInequalities.KLS.LogConcave.contDiff_cutoff ((n : ℝ) + 1)) (FunctionalInequalities.KLS.LogConcave.hasCompactSupport_cutoff (hpos n)) u).toLp _‖ :=
            norm_add_le _ _
      _ ≤ _ := by linarith [hbound n]
  exact norm_eq_zero.mp (le_antisymm hzero (norm_nonneg u))
