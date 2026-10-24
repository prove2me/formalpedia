-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.cumulant_eq_taylorComp_cond_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:42:11.160329+00:00
-- url     : https://prove2.me/submissions/9bce3faa-1da1-462a-89c0-cd2148ee2fee

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_LocalDerivatives
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
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
section CondHelpers
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- The cumulant tensor as the Faà di Bruno composition of the Taylor jets of `log` at `1` and of
the Laplace transform at `0`. -/
theorem solution (μ : Measure E) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (k : ℕ) :
    FunctionalInequalities.Analysis.BakryEmery.cumulant μ k = (ftaylorSeriesWithin ℝ Real.log {0}ᶜ 1).taylorComp
      (ftaylorSeriesWithin ℝ (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂μ) (Metric.ball 0 r) 0) k := by
  have hgi : ∀ t < r,
      Integrable (fun x : E => Real.exp (t * ‖x‖) * ‖(1 : ℝ)‖) μ := by
    intro t ht
    refine hexp.mono' ?_ ?_
    · fun_prop
    · filter_upwards [] with x
      simp only [norm_one, mul_one, Real.norm_of_nonneg (Real.exp_pos _).le]
      by_cases ht0 : 0 ≤ t
      · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ht.le (norm_nonneg x))
      · calc
          Real.exp (t * ‖x‖) ≤ 1 := Real.exp_le_one_iff.mpr
            (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ht0) (norm_nonneg x))
          _ ≤ Real.exp (r * ‖x‖) := Real.one_le_exp_iff.mpr
            (mul_nonneg hr.le (norm_nonneg x))
  have hZ : ContDiffOn ℝ ∞ (fun z : E => ∫ x, Real.exp ⟪z, x⟫ ∂μ)
      (Metric.ball 0 r) := by
    simpa only [smul_eq_mul, mul_one] using
      FunctionalInequalities.Analysis.BakryEmery.weighted_integral_contDiffOn μ measurable_const.aestronglyMeasurable hgi
  have hpos : ∀ z ∈ Metric.ball (0 : E) r, 0 < ∫ x, Real.exp ⟪z, x⟫ ∂μ := by
    intro z hz
    have hz' : ‖z‖ < r := by simpa using hz
    have hzint : Integrable (fun x : E => Real.exp ⟪z, x⟫) μ := by
      refine (hgi ‖z‖ hz').mono' ?_ ?_
      · exact (by fun_prop : Continuous (fun x : E => Real.exp ⟪z, x⟫)).aestronglyMeasurable
      · filter_upwards [] with x
        simp only [norm_one, mul_one, Real.norm_of_nonneg (Real.exp_pos _).le]
        exact Real.exp_le_exp.mpr (real_inner_le_norm z x)
    exact integral_exp_pos hzint
  have hU : UniqueDiffOn ℝ (Metric.ball (0 : E) r) := Metric.isOpen_ball.uniqueDiffOn
  have hf : HasFTaylorSeriesUpToOn k (fun z : E => ∫ x, Real.exp ⟪z, x⟫ ∂μ)
      (ftaylorSeriesWithin ℝ (fun z : E => ∫ x, Real.exp ⟪z, x⟫ ∂μ) (Metric.ball 0 r))
      (Metric.ball 0 r) :=
    (hZ.of_le (WithTop.coe_le_coe.mpr le_top)).ftaylorSeriesWithin hU
  have hg : HasFTaylorSeriesUpToOn k Real.log (ftaylorSeriesWithin ℝ Real.log {0}ᶜ) {0}ᶜ :=
    (Real.contDiffOn_log (n := k)).ftaylorSeriesWithin isOpen_compl_singleton.uniqueDiffOn
  have hmaps : Set.MapsTo (fun z : E => ∫ x, Real.exp ⟪z, x⟫ ∂μ) (Metric.ball 0 r) {0}ᶜ :=
    fun z hz => (hpos z hz).ne'
  have hcomp := hg.comp hf hmaps
  have h0 : (0 : E) ∈ Metric.ball (0 : E) r := Metric.mem_ball_self hr
  have heq := hcomp.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hU h0
  have hZ0 : (∫ x, Real.exp ⟪(0 : E), x⟫ ∂μ) = 1 := by simp
  rw [hZ0] at heq
  have hlog : FunctionalInequalities.Analysis.BakryEmery.logLaplace μ = Real.log ∘ (fun z : E => ∫ x, Real.exp ⟪z, x⟫ ∂μ) := rfl
  unfold FunctionalInequalities.Analysis.BakryEmery.cumulant
  rw [hlog, ← iteratedFDerivWithin_of_isOpen k Metric.isOpen_ball h0, ← heq]
