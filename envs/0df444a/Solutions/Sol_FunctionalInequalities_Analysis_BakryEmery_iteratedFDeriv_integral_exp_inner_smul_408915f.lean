-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_integral_exp_inner_smul_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:43:23.037837+00:00
-- url     : https://prove2.me/submissions/0b49a7bd-adb7-40b8-bbe6-b111b0afe7db

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
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
section IntegralCalculus
omit [CompleteSpace E]
section NormedSpace
variable {F : Type*}
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- The iterated derivatives of the Laplace-type integral are weighted moments. -/
theorem solution (μ : Measure E) {g : E → F}
    (hg : AEStronglyMeasurable g μ)
    (hgi : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖) * ‖g x‖) μ) (d : ℕ) (z : E)
    (h : Fin d → E) :
    iteratedFDeriv ℝ d (fun z => ∫ x, Real.exp ⟪z, x⟫ • g x ∂μ) z h =
      ∫ x, (Real.exp ⟪z, x⟫ * ∏ j, ⟪x, h j⟫) • g x ∂μ := by
  classical
  induction d generalizing g with
  | zero => simp
  | succ d IH =>
    let N : E → F := fun w => ∫ x, Real.exp ⟪w, x⟫ • g x ∂μ
    let a := h (Fin.last d)
    let ev : (E →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F a
    let g' : E → F := fun x => FunctionalInequalities.Analysis.BakryEmery.weightedExpD g x a
    have hg' : AEStronglyMeasurable g' μ :=
      ev.continuous.comp_aestronglyMeasurable (FunctionalInequalities.Analysis.BakryEmery.weightedExpD_meas hg)
    have hgi' : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖) * ‖g' x‖) μ := by
      intro r
      refine ((FunctionalInequalities.Analysis.BakryEmery.weightedExpD_integrable hg hgi r).const_mul ‖a‖).mono' ?_ ?_
      · exact (by fun_prop : Continuous (fun x : E => Real.exp (r * ‖x‖))).aestronglyMeasurable.mul hg'.norm
      · filter_upwards [] with x
        rw [Real.norm_of_nonneg (by positivity)]
        calc
          Real.exp (r * ‖x‖) * ‖g' x‖ ≤
              Real.exp (r * ‖x‖) * (‖FunctionalInequalities.Analysis.BakryEmery.weightedExpD g x‖ * ‖a‖) := by
            gcongr
            exact (FunctionalInequalities.Analysis.BakryEmery.weightedExpD g x).le_opNorm a
          _ = ‖a‖ * (Real.exp (r * ‖x‖) * ‖FunctionalInequalities.Analysis.BakryEmery.weightedExpD g x‖) := by ring
    have hN : ContDiff ℝ ∞ N :=
      FunctionalInequalities.Analysis.BakryEmery.contDiff_integral_exp_inner_smul_of_integrable μ hg hgi
    have hfd : fderiv ℝ N =
        fun w => ∫ x, Real.exp ⟪w, x⟫ • FunctionalInequalities.Analysis.BakryEmery.weightedExpD g x ∂μ := by
      funext w
      exact (FunctionalInequalities.Analysis.BakryEmery.weightedExp_integral_hasFDeriv μ hg hgi w).fderiv
    have heval : ev ∘ fderiv ℝ N =
        fun w => ∫ x, Real.exp ⟪w, x⟫ • g' x ∂μ := by
      funext w
      rw [Function.comp_apply, hfd]
      change (∫ x, Real.exp ⟪w, x⟫ • FunctionalInequalities.Analysis.BakryEmery.weightedExpD g x ∂μ) a = _
      rw [ContinuousLinearMap.integral_apply
        (FunctionalInequalities.Analysis.BakryEmery.weightedExp_integrable μ (FunctionalInequalities.Analysis.BakryEmery.weightedExpD_meas hg)
          (FunctionalInequalities.Analysis.BakryEmery.weightedExpD_integrable hg hgi) w)]
      rfl
    rw [iteratedFDeriv_succ_apply_right]
    change ev (iteratedFDeriv ℝ d (fderiv ℝ N) z (Fin.init h)) = _
    calc
      ev (iteratedFDeriv ℝ d (fderiv ℝ N) z (Fin.init h)) =
          iteratedFDeriv ℝ d (ev ∘ fderiv ℝ N) z (Fin.init h) := by
        have hN' : ContDiff ℝ ∞ (fderiv ℝ N) := hN.fderiv_right (by simp)
        have H := ev.iteratedFDeriv_comp_left
          (hN'.contDiffAt (x := z)) (i := d) (by exact_mod_cast le_top (a := (d : ℕ∞)))
        exact (congrArg (fun T => T (Fin.init h)) H).symm
      _ = ∫ x, (Real.exp ⟪z, x⟫ * ∏ j, ⟪x, Fin.init h j⟫) • g' x ∂μ := by
        rw [heval]
        exact IH hg' hgi' (Fin.init h)
      _ = ∫ x, (Real.exp ⟪z, x⟫ * ∏ j, ⟪x, h j⟫) • g x ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [g', FunctionalInequalities.Analysis.BakryEmery.weightedExpD, ContinuousLinearMap.smulRight_apply,
          innerSL_apply_apply, smul_smul]
        rw [Fin.prod_univ_castSucc]
        simp only [a, Fin.init_def, mul_assoc]
