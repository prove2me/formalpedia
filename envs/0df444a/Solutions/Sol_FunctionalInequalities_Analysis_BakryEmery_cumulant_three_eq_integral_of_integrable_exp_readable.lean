-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.cumulant_three_eq_integral_of_integrable_exp_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:26:37.341258+00:00
-- url     : https://prove2.me/submissions/cd7e6877-7284-4212-9234-5883ed121270

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
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem FunctionalInequalities.Analysis.BakryEmery.second_mul {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (hg : ContDiffAt ℝ ∞ g x) (v w : E) (hf0 : f x = 0) (hg0 : g x = 1)
    (hg1 : fderiv ℝ g x = 0) :
    iteratedFDeriv ℝ 2 (fun y => f y * g y) x ![v, w] =
      iteratedFDeriv ℝ 2 f x ![v, w] := by
  have hdf := hf.fderiv_right (m := ∞) (by simp)
  have hdg := hg.fderiv_right (m := ∞) (by simp)
  have hfw : DifferentiableAt ℝ (fun y => fderiv ℝ f y w) x :=
    ((ContinuousLinearMap.apply ℝ ℝ w).contDiff.contDiffAt.comp x hdf).differentiableAt (by simp)
  have hgw : DifferentiableAt ℝ (fun y => fderiv ℝ g y w) x :=
    ((ContinuousLinearMap.apply ℝ ℝ w).contDiff.contDiffAt.comp x hdg).differentiableAt (by simp)
  have heq : (fun y => fderiv ℝ (fun z => f z * g z) y w) =ᶠ[𝓝 x]
      (fun y => f y * fderiv ℝ g y w + g y * fderiv ℝ f y w) := by
    have hfe := (hf.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).eventually (by norm_num)
    have hge := (hg.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).eventually (by norm_num)
    filter_upwards [hfe, hge] with y hyf hyg
    rw [fderiv_fun_mul (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))]
    simp
  rw [second_apply (hf.mul hg), second_apply hf, heq.fderiv_eq]
  rw [fderiv_fun_add (f := fun y => f y * fderiv ℝ g y w)
    (g := fun y => g y * fderiv ℝ f y w)
    ((hf.differentiableAt (by simp)).mul hgw)
    ((hg.differentiableAt (by simp)).mul hfw)]
  rw [fderiv_fun_mul (hf.differentiableAt (by simp)) hgw,
    fderiv_fun_mul (hg.differentiableAt (by simp)) hfw]
  simp [hf0, hg0, hg1]
theorem FunctionalInequalities.Analysis.BakryEmery.norm_exp_weights {μ : Measure E} {r : ℝ}
    (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) :
    ∀ t < r, Integrable (fun x => Real.exp (t * ‖x‖) * ‖(1 : ℝ)‖) μ := by
  intro t ht
  simp only [norm_one, mul_one]
  refine hexp.mono' (by fun_prop) ?_
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ht.le (norm_nonneg _))
/-- **Third cumulant of a centered law with one exponential moment**: if `∫ e^{r‖x‖} dμ < ∞` for some
`r > 0` and `μ` is centered, then `κ₃(u, v, w) = ∫ ⟪u,x⟫⟪v,x⟫⟪w,x⟫ dμ` (no global exponential moments). -/
theorem solution (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    (hc : ∀ v : E, ∫ x, ⟪v, x⟫ ∂μ = 0) (u v w : E) :
    FunctionalInequalities.Analysis.BakryEmery.cumulant μ 3 ![u, v, w] = ∫ x, ⟪u, x⟫ * ⟪v, x⟫ * ⟪w, x⟫ ∂μ := by
  let Z : E → ℝ := fun z => ∫ x, Real.exp ⟪z, x⟫ • (1 : ℝ) ∂μ
  let N : E → ℝ := fun z => ∫ x, Real.exp ⟪z, x⟫ • ⟪w, x⟫ ∂μ
  let F : E → ℝ := fun z => fderiv ℝ (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ) z w
  have hz : ‖(0 : E)‖ < r := by simpa
  have hL : ContDiffAt ℝ ∞ (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ) 0 :=
    (FunctionalInequalities.Analysis.BakryEmery.contDiffOn_logLaplace_ball_readable μ hr hexp).contDiffAt (Metric.ball_mem_nhds 0 hr)
  have hF : ContDiffAt ℝ ∞ F 0 :=
    (ContinuousLinearMap.apply ℝ ℝ w).contDiff.contDiffAt.comp 0
      (hL.fderiv_right (m := ∞) (by simp))
  have hZ : ContDiffAt ℝ ∞ Z 0 :=
    (FunctionalInequalities.Analysis.BakryEmery.weighted_integral_contDiffOn μ measurable_const.aestronglyMeasurable
      (FunctionalInequalities.Analysis.BakryEmery.norm_exp_weights hexp)).contDiffAt (Metric.ball_mem_nhds 0 hr)
  have hZ0 : Z 0 = 1 := by simp [Z]
  have hF0 : F 0 = 0 := by
    dsimp [F]
    rw [← FunctionalInequalities.Analysis.BakryEmery.tiltAverage_inner_eq_fderiv_logLaplace_of_lt_readable μ hexp hz w]
    simpa [FunctionalInequalities.Analysis.BakryEmery.tiltAverage, FunctionalInequalities.Analysis.BakryEmery.expTilt] using hc w
  have hZ1 : fderiv ℝ Z 0 = 0 := by
    ext a
    have h := FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_weightedExp_integral_of_lt μ
      (g := fun _ : E => (1 : ℝ)) measurable_const.aestronglyMeasurable
      (FunctionalInequalities.Analysis.BakryEmery.norm_exp_weights hexp) 1 (0 : E) hz ![a]
    have h' : fderiv ℝ Z 0 a = ∫ x, ⟪a, x⟫ ∂μ := by
      simpa [Z, iteratedFDeriv_one_apply, real_inner_comm] using h
    exact h'.trans (hc a)
  have hNZ : N =ᶠ[𝓝 0] (fun z => F z * Z z) := by
    filter_upwards [Metric.ball_mem_nhds (0 : E) hr] with z hzmem
    have hz' : ‖z‖ < r := by simpa using hzmem
    have hi := FunctionalInequalities.Analysis.BakryEmery.integrable_exp_inner_smul_of_lt μ (g := fun _ : E => (1 : ℝ))
      measurable_const.aestronglyMeasurable (FunctionalInequalities.Analysis.BakryEmery.norm_exp_weights hexp) hz'
    have hp : (∫ x, Real.exp ⟪z, x⟫ ∂μ) ≠ 0 :=
      (integral_exp_pos (by simpa only [smul_eq_mul, mul_one] using hi)).ne'
    dsimp [N, F, Z]
    rw [← FunctionalInequalities.Analysis.BakryEmery.tiltAverage_inner_eq_fderiv_logLaplace_of_lt_readable μ hexp hz' w]
    rw [FunctionalInequalities.Analysis.BakryEmery.tiltAverage, FunctionalInequalities.Analysis.BakryEmery.expTilt, integral_tilted]
    simp only [smul_eq_mul, mul_one, div_eq_mul_inv]
    rw [show (fun x => Real.exp ⟪z, x⟫ * (∫ y, Real.exp ⟪z, y⟫ ∂μ)⁻¹ * ⟪w, x⟫) =
      (fun x => (Real.exp ⟪z, x⟫ * ⟪w, x⟫) * (∫ y, Real.exp ⟪z, y⟫ ∂μ)⁻¹) by
        funext x; ring]
    rw [integral_mul_const]
    field_simp
  have hsecond := FunctionalInequalities.Analysis.BakryEmery.second_mul hF hZ u v hF0 hZ0 hZ1
  have hm := FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_weightedExp_integral_of_lt μ
    (g := fun x => ⟪w, x⟫)
    (by fun_prop : Continuous (fun x : E => ⟪w, x⟫)).aestronglyMeasurable
    (FunctionalInequalities.Analysis.BakryEmery.inner_exp_weights_readable hexp w) 2 (0 : E) hz ![u, v]
  have hm' : iteratedFDeriv ℝ 2 N 0 ![u, v] =
      ∫ x, ⟪u, x⟫ * ⟪v, x⟫ * ⟪w, x⟫ ∂μ := by
    simpa [N, Fin.prod_univ_two, smul_eq_mul, real_inner_comm,
      mul_comm, mul_left_comm, mul_assoc] using hm
  have hNF : iteratedFDeriv ℝ 2 N 0 ![u, v] = iteratedFDeriv ℝ 2 F 0 ![u, v] := by
    rw [(hNZ.iteratedFDeriv ℝ 2).self_of_nhds]
    exact hsecond
  have hcomm : iteratedFDeriv ℝ 2 F 0 ![u, v] =
      iteratedFDeriv ℝ 2 (fderiv ℝ (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ)) 0 ![u, v] w := by
    have H := (ContinuousLinearMap.apply ℝ ℝ w).iteratedFDeriv_comp_left
      (hL.fderiv_right (m := ∞) (by simp)) (i := 2) (by norm_cast)
    exact congrArg (fun T => T ![u, v]) H
  unfold FunctionalInequalities.Analysis.BakryEmery.cumulant
  rw [iteratedFDeriv_succ_apply_right]
  have hinit : Fin.init ![u, v, w] = ![u, v] := by
    ext i
    fin_cases i <;> rfl
  rw [hinit]
  change iteratedFDeriv ℝ 2 (fderiv ℝ (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ)) 0 ![u, v] w = _
  rw [← hcomm, ← hNF, hm']
