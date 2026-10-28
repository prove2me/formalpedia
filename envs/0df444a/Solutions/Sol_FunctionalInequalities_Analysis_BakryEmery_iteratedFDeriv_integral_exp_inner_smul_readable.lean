-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_integral_exp_inner_smul_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:25:15.115636+00:00
-- url     : https://prove2.me/submissions/5c1c7f52-acef-4aa1-bf66-c96e6e569f44

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable

noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff ENNReal
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section IntegralCalculus
omit [CompleteSpace E]
section NormedSpace
variable {F : Type*}
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
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
