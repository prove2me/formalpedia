-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.tiltAverage_inner_eq_fderiv_logLaplace_of_lt_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:43:05.191031+00:00
-- url     : https://prove2.me/submissions/e5c9afbc-a527-48f4-9088-3a2170dfa46f

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
section LaplaceCalculus
omit [CompleteSpace E]
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- **Local tilt-average/derivative identity**: `F_{⟪v,·⟫}(z) = ∂_v Λ_μ(z)` for `‖z‖ < r`, assuming
only the single exponential moment `∫ e^{r‖x‖} dμ < ∞`. -/
theorem solution (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
    {r : ℝ} (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) {z : E} (hz : ‖z‖ < r) (v : E) :
    FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ (fun x => ⟪v, x⟫) z = fderiv ℝ (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ) z v := by
      let g : E → ℝ := fun _ => 1
      have hg : AEStronglyMeasurable g μ := by
        exact aestronglyMeasurable_const
      have hr : 0 ≤ r := by
        linarith [norm_nonneg z]
      have hgi :
          ∀ t < r, Integrable (fun x => Real.exp (t * ‖x‖) * ‖g x‖) μ := by
        intro t ht
        apply hexp.mono' (by fun_prop)
        filter_upwards with x
        simp only [g, norm_one, mul_one]
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        by_cases h : 0 ≤ t
        · apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_right (le_of_lt ht) (norm_nonneg x)
        · have htx : t * ‖x‖ ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) (norm_nonneg x)
          have hzero : 0 ≤ r * ‖x‖ :=
            mul_nonneg hr (norm_nonneg x)
          calc
            Real.exp (t * ‖x‖) ≤ 1 := by
              simpa using Real.exp_le_one_iff.mpr htx
            _ ≤ Real.exp (r * ‖x‖) := by
              simpa using Real.one_le_exp_iff.mpr hzero
      have hd := FunctionalInequalities.Analysis.BakryEmery.weightedExp_integral_hasFDerivAt_of_lt
        (μ := μ) hg hgi hz
      have hd' :
          HasFDerivAt
            (fun w : E => ∫ x, Real.exp ⟪w, x⟫ ∂μ)
            (∫ x, Real.exp ⟪z, x⟫ • FunctionalInequalities.Analysis.BakryEmery.weightedExpD g x ∂μ) z := by
        simpa [g, smul_eq_mul, mul_one] using hd
      have hi : Integrable (fun x => Real.exp ⟪z, x⟫) μ := by
        apply hexp.mono' (by fun_prop)
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        calc
          ⟪z, x⟫ ≤ ‖z‖ * ‖x‖ := real_inner_le_norm z x
          _ ≤ r * ‖x‖ := by
            exact mul_le_mul_of_nonneg_right hz.le (norm_nonneg x)
      have hp : 0 < ∫ x, Real.exp ⟪z, x⟫ ∂μ :=
        integral_exp_pos hi
      have hlog := hd'.log hp.ne'
      change
        FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ (fun x => ⟪v, x⟫) z =
          (fderiv ℝ (fun w : E => Real.log (∫ x, Real.exp ⟪w, x⟫ ∂μ)) z) v
      rw [hlog.fderiv]
      have hwd :
          Integrable
            (fun x =>
              Real.exp (‖z‖ * ‖x‖) * ‖FunctionalInequalities.Analysis.BakryEmery.weightedExpD g x‖) μ :=
        (FunctionalInequalities.Analysis.BakryEmery.weightedExpD_integrable_lt (μ := μ) hg hgi) ‖z‖ hz
      have hwi :
          Integrable
            (fun x => Real.exp ⟪z, x⟫ • FunctionalInequalities.Analysis.BakryEmery.weightedExpD g x) μ := by
        refine hwd.mono' ?_ ?_
        · change AEStronglyMeasurable
            (fun x => Real.exp ⟪z, x⟫ •
              (innerSL ℝ x).smulRight (1 : ℝ)) μ
          fun_prop
        · filter_upwards with x
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact
            mul_le_mul_of_nonneg_right
              (Real.exp_le_exp.mpr (real_inner_le_norm z x))
              (norm_nonneg (FunctionalInequalities.Analysis.BakryEmery.weightedExpD g x))
      unfold FunctionalInequalities.Analysis.BakryEmery.tiltAverage FunctionalInequalities.Analysis.BakryEmery.expTilt
      rw [integral_tilted]
      conv_rhs =>
        rw [smul_apply]
      rw [ContinuousLinearMap.integral_apply hwi]
      simp_rw [smul_eq_mul, div_eq_mul_inv]
      rw [← integral_const_mul]
      congr 1
      funext x
      simp [g, FunctionalInequalities.Analysis.BakryEmery.weightedExpD, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
        smul_eq_mul, real_inner_comm]
      ring
