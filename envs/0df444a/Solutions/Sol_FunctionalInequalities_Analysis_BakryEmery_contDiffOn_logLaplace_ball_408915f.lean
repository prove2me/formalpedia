-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.contDiffOn_logLaplace_ball_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:41:21.603057+00:00
-- url     : https://prove2.me/submissions/04be237a-f5b8-430b-ba22-29dd0acde55b

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
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
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory
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
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section CumulantEstimates
omit [CompleteSpace E]
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
open scoped ContDiff in
/-- **Local smoothness of `Λ_μ`** (BKL p. 29, "finite and smooth in a neighborhood of the origin"):
one positive norm-exponential moment `∫ e^{r‖x‖} dμ < ∞` makes `Λ_μ` `C^∞` on the open ball of
radius `r`. The local integral identities are in `Tilt/Local.lean`. -/
theorem solution (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ] {r : ℝ}
    (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) :
    ContDiffOn ℝ ∞ (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ) (Metric.ball 0 r) := by
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
  apply hZ.log
  intro z hz
  have hz' : ‖z‖ < r := by simpa using hz
  have hzint : Integrable (fun x : E => Real.exp ⟪z, x⟫) μ := by
    refine (hgi ‖z‖ hz').mono' ?_ ?_
    · exact (by fun_prop : Continuous (fun x : E => Real.exp ⟪z, x⟫)).aestronglyMeasurable
    · filter_upwards [] with x
      simp only [norm_one, mul_one, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (real_inner_le_norm z x)
  exact (integral_exp_pos hzint).ne'
