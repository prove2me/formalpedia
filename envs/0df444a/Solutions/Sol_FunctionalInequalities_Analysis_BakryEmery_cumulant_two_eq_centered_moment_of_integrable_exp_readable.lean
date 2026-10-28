-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.cumulant_two_eq_centered_moment_of_integrable_exp_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:26:38.531038+00:00
-- url     : https://prove2.me/submissions/276ea533-a242-431c-836f-00e963738775

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_contDiffOn_logLaplace_ball_readable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_inner_exp_weights_readable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_tiltAverage_inner_eq_fderiv_logLaplace_of_lt_readable

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem FunctionalInequalities.Analysis.BakryEmery.second_apply {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (v w : E) :
    iteratedFDeriv ℝ 2 f x ![v, w] = fderiv ℝ (fun y => fderiv ℝ f y w) x v := by
  rw [(hf.differentiableAt_iteratedFDeriv (m := 1) (by norm_num)).iteratedFDeriv_succ_apply_left']
  simp only [iteratedFDeriv_one_apply, Fin.tail, Matrix.cons_val_zero, Matrix.cons_val_succ]
theorem FunctionalInequalities.Analysis.BakryEmery.norm_exp_weights {μ : Measure E} {r : ℝ}
    (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) :
    ∀ t < r, Integrable (fun x => Real.exp (t * ‖x‖) * ‖(1 : ℝ)‖) μ := by
  intro t ht
  simp only [norm_one, mul_one]
  refine hexp.mono' (by fun_prop) ?_
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ht.le (norm_nonneg _))
section SecondCumulant
/-- **Second cumulant from one exponential moment**: for any probability law with `∫ e^{r‖x‖} dμ < ∞` for
some `r > 0` (no centering), `κ₂(u, v) = ∫⟪u,x⟫⟪v,x⟫ dμ − (∫⟪u,x⟫ dμ)(∫⟪v,x⟫ dμ)`. -/
theorem solution (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (u v : E) :
    FunctionalInequalities.Analysis.BakryEmery.cumulant μ 2 ![u, v] =
      (∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ) - (∫ x, ⟪u, x⟫ ∂μ) * (∫ x, ⟪v, x⟫ ∂μ) := by
  let Z : E → ℝ := fun z => ∫ x, Real.exp ⟪z, x⟫ • (1 : ℝ) ∂μ
  let N : E → ℝ := fun z => ∫ x, Real.exp ⟪z, x⟫ • ⟪v, x⟫ ∂μ
  let F : E → ℝ := fun z => fderiv ℝ (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ) z v
  have hz : ‖(0 : E)‖ < r := by simpa
  have hL : ContDiffAt ℝ ∞ (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ) 0 :=
    (FunctionalInequalities.Analysis.BakryEmery.contDiffOn_logLaplace_ball_readable μ hr hexp).contDiffAt (Metric.ball_mem_nhds 0 hr)
  have hF : ContDiffAt ℝ ∞ F 0 :=
    (ContinuousLinearMap.apply ℝ ℝ v).contDiff.contDiffAt.comp 0
      (hL.fderiv_right (m := ∞) (by simp))
  have hZ : ContDiffAt ℝ ∞ Z 0 :=
    (FunctionalInequalities.Analysis.BakryEmery.weighted_integral_contDiffOn μ measurable_const.aestronglyMeasurable
      (FunctionalInequalities.Analysis.BakryEmery.norm_exp_weights hexp)).contDiffAt (Metric.ball_mem_nhds 0 hr)
  have hZ0 : Z 0 = 1 := by simp [Z]
  have hF0 : F 0 = ∫ x, ⟪v, x⟫ ∂μ := by
    dsimp [F]
    rw [← FunctionalInequalities.Analysis.BakryEmery.tiltAverage_inner_eq_fderiv_logLaplace_of_lt_readable μ hexp hz v]
    simp [FunctionalInequalities.Analysis.BakryEmery.tiltAverage, FunctionalInequalities.Analysis.BakryEmery.expTilt]
  have hZ1 : fderiv ℝ Z 0 u = ∫ x, ⟪u, x⟫ ∂μ := by
    have h := FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_weightedExp_integral_of_lt μ
      (g := fun _ : E => (1 : ℝ)) measurable_const.aestronglyMeasurable
      (FunctionalInequalities.Analysis.BakryEmery.norm_exp_weights hexp) 1 (0 : E) hz ![u]
    simpa [Z, iteratedFDeriv_one_apply, real_inner_comm] using h
  have hN1 : fderiv ℝ N 0 u = ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ := by
    have h := FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_weightedExp_integral_of_lt μ
      (g := fun x => ⟪v, x⟫)
      (by fun_prop : Continuous (fun x : E => ⟪v, x⟫)).aestronglyMeasurable
      (FunctionalInequalities.Analysis.BakryEmery.inner_exp_weights_readable hexp v) 1 (0 : E) hz ![u]
    simpa [N, iteratedFDeriv_one_apply, smul_eq_mul, real_inner_comm] using h
  have hNZ : N =ᶠ[𝓝 0] (fun z => F z * Z z) := by
    filter_upwards [Metric.ball_mem_nhds (0 : E) hr] with z hzmem
    have hz' : ‖z‖ < r := by simpa using hzmem
    have hi := FunctionalInequalities.Analysis.BakryEmery.integrable_exp_inner_smul_of_lt μ (g := fun _ : E => (1 : ℝ))
      measurable_const.aestronglyMeasurable (FunctionalInequalities.Analysis.BakryEmery.norm_exp_weights hexp) hz'
    have hp : (∫ x, Real.exp ⟪z, x⟫ ∂μ) ≠ 0 :=
      (integral_exp_pos (by simpa only [smul_eq_mul, mul_one] using hi)).ne'
    dsimp [N, F, Z]
    rw [← FunctionalInequalities.Analysis.BakryEmery.tiltAverage_inner_eq_fderiv_logLaplace_of_lt_readable μ hexp hz' v]
    rw [FunctionalInequalities.Analysis.BakryEmery.tiltAverage, FunctionalInequalities.Analysis.BakryEmery.expTilt, integral_tilted]
    simp only [smul_eq_mul, mul_one, div_eq_mul_inv]
    rw [show (fun x => Real.exp ⟪z, x⟫ * (∫ y, Real.exp ⟪z, y⟫ ∂μ)⁻¹ * ⟪v, x⟫) =
      (fun x => (Real.exp ⟪z, x⟫ * ⟪v, x⟫) * (∫ y, Real.exp ⟪z, y⟫ ∂μ)⁻¹) by
        funext x; ring]
    rw [integral_mul_const]
    field_simp
  have hD := congrArg (fun L : E →L[ℝ] ℝ => L u) hNZ.fderiv_eq
  rw [fderiv_fun_mul (hF.differentiableAt (by simp)) (hZ.differentiableAt (by simp))] at hD
  simp only [add_apply, smul_apply, smul_eq_mul] at hD
  rw [hF0, hZ1, hZ0, one_mul, hN1] at hD
  change iteratedFDeriv ℝ 2 (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ) 0 ![u, v] = _
  rw [FunctionalInequalities.Analysis.BakryEmery.second_apply hL]
  change fderiv ℝ F 0 u = _
  nlinarith
