-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.tiltAverage_inner_eq_fderiv_logLaplace_of_lt_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:25:10.431378+00:00
-- url     : https://prove2.me/submissions/c7206455-041e-43ba-9911-8581ab5fdd94

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section LaplaceCalculus
omit [CompleteSpace E]
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
