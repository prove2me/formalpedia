-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.tiltAverage_inner_eq_fderiv_logLaplace_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:26:09.146239+00:00
-- url     : https://prove2.me/submissions/4b173a23-f240-49b6-86c9-f2a7595ce116

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section LaplaceCalculus
omit [CompleteSpace E]
omit [FiniteDimensional ℝ E] in
private lemma FunctionalInequalities.Analysis.BakryEmery.bkl_integrable_exp_inner (μ : Measure E) [IsFiniteMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (z : E) :
    Integrable (fun x => Real.exp ⟪z, x⟫) μ := by
  refine (hexp ‖z‖).mono'
    ((continuous_const.inner continuous_id).rexp.aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (real_inner_le_norm z x)
private lemma FunctionalInequalities.Analysis.BakryEmery.bkl_hasFDerivAt_laplace (μ : Measure E) [IsFiniteMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (z : E) :
    HasFDerivAt (fun y => ∫ x, Real.exp ⟪y, x⟫ ∂μ)
      (∫ x, Real.exp ⟪z, x⟫ • innerSL ℝ x ∂μ) z := by
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y x => Real.exp ⟪y, x⟫)
    (F' := fun y x => Real.exp ⟪y, x⟫ • innerSL ℝ x)
    (s := Metric.ball z 1)
    (bound := fun x => Real.exp ((‖z‖ + 2) * ‖x‖))
    (Metric.ball_mem_nhds z zero_lt_one) ?_
    (bkl_integrable_exp_inner μ hexp z) ?_ ?_
    (hexp (‖z‖ + 2)) ?_
  · exact Filter.Eventually.of_forall fun y =>
      (continuous_const.inner continuous_id).rexp.aestronglyMeasurable
  · exact ((continuous_const.inner continuous_id).rexp.smul
      (innerSL ℝ).continuous).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x y hy => by
      have hy' : ‖y‖ ≤ ‖z‖ + 1 := by
        have hdist : ‖y - z‖ < 1 := by
          simpa [dist_eq_norm] using hy
        calc
          ‖y‖ ≤ ‖z‖ + ‖y - z‖ := by
            simpa [add_comm, norm_sub_rev] using norm_le_norm_add_norm_sub z y
          _ ≤ ‖z‖ + 1 := by linarith
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        innerSL_apply_norm]
      calc
        Real.exp ⟪y, x⟫ * ‖x‖ ≤
            Real.exp ((‖z‖ + 1) * ‖x‖) * Real.exp ‖x‖ := by
          exact mul_le_mul
            (Real.exp_le_exp.mpr
              ((real_inner_le_norm y x).trans
                (mul_le_mul_of_nonneg_right hy' (norm_nonneg x))))
            (le_trans (by linarith : ‖x‖ ≤ ‖x‖ + 1)
              (Real.add_one_le_exp ‖x‖))
            (norm_nonneg x) (Real.exp_pos _).le
        _ = Real.exp ((‖z‖ + 2) * ‖x‖) := by
          rw [← Real.exp_add]
          congr 1
          ring
  · exact Filter.Eventually.of_forall fun x y _ => by
      simpa only [innerSL_apply_apply, real_inner_comm] using
        (innerSL ℝ x).hasFDerivAt.exp
/-- The tilt average of a linear function is a derivative of `Λ_μ`: `F_ℓ(z) = ⟪v, ∇Λ_μ(z)⟫` for
`ℓ = ⟪v, ·⟫` (proof of BKL Proposition 7.1). -/
theorem solution (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (v z : E) :
    FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ (fun x => ⟪v, x⟫) z = fderiv ℝ (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ) z v := by
  have hi := FunctionalInequalities.Analysis.BakryEmery.bkl_integrable_exp_inner μ hexp z
  have hd := FunctionalInequalities.Analysis.BakryEmery.bkl_hasFDerivAt_laplace μ hexp z
  have hp : (∫ x, Real.exp ⟪z, x⟫ ∂μ) ≠ 0 := (integral_exp_pos hi).ne'
  have hlog := hd.log hp
  change FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ (fun x => ⟪v, x⟫) z =
    fderiv ℝ (fun y => Real.log (∫ x, Real.exp ⟪y, x⟫ ∂μ)) z v
  rw [hlog.fderiv]
  change (∫ x, ⟪v, x⟫ ∂(μ.tilted fun x => ⟪z, x⟫)) =
    (∫ x, Real.exp ⟪z, x⟫ ∂μ)⁻¹ *
      (∫ x, Real.exp ⟪z, x⟫ • innerSL ℝ x ∂μ) v
  rw [integral_tilted]
  have hdi : Integrable (fun x => Real.exp ⟪z, x⟫ • innerSL ℝ x) μ := by
    refine (hexp (‖z‖ + 1)).mono' ?_ ?_
    · exact ((continuous_const.inner continuous_id).rexp.smul
        (innerSL ℝ).continuous).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          innerSL_apply_norm]
        calc
          Real.exp ⟪z, x⟫ * ‖x‖ ≤
              Real.exp (‖z‖ * ‖x‖) * Real.exp ‖x‖ :=
            mul_le_mul
              (Real.exp_le_exp.mpr (real_inner_le_norm z x))
              (le_trans (by linarith : ‖x‖ ≤ ‖x‖ + 1)
                (Real.add_one_le_exp ‖x‖))
              (norm_nonneg x) (Real.exp_pos _).le
          _ = Real.exp ((‖z‖ + 1) * ‖x‖) := by
            rw [← Real.exp_add]
            congr 1
            ring
  rw [ContinuousLinearMap.integral_apply hdi]
  simp_rw [smul_apply, smul_eq_mul, innerSL_apply_apply, real_inner_comm,
    div_eq_mul_inv]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring
