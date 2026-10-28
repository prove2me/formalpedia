-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.graph_log_integral_hasDerivAt_zero_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:20:53.83208+00:00
-- url     : https://prove2.me/submissions/ab5f533d-7746-43f8-8af4-b01b990cffc9

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Derivatives

open MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Line
open scoped RealInnerProductSpace
open FunctionalInequalities.KLS.LogConcave.Suspension
open scoped Topology ContDiff
private theorem FunctionalInequalities.KLS.LogConcave.Suspension.local_laplace_derivative_and_integrable {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) {r : ℝ}
    (hexp : Integrable (fun y => Real.exp (r * ‖y‖)) ν) {q : E} (hq : ‖q‖ < r) :
    HasFDerivAt (fun w : E => ∫ y, Real.exp ⟪w, y⟫ ∂ν)
      (∫ y, Real.exp ⟪q, y⟫ • weightedExpD (fun _ : E => (1 : ℝ)) y ∂ν) q ∧
      Integrable (fun y => Real.exp ⟪q, y⟫ • weightedExpD (fun _ : E => (1 : ℝ)) y) ν := by
  have hgi : ∀ t < r, Integrable (fun y : E => Real.exp (t * ‖y‖) * ‖(1 : ℝ)‖) ν := by
    intro t ht
    refine hexp.mono' ?_ ?_
    · fun_prop
    · filter_upwards [] with y
      simp only [norm_one, mul_one, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ht.le (norm_nonneg y))
  have hDgi := weightedExpD_integrable_lt (g := fun _ : E => (1 : ℝ))
    measurable_const.aestronglyMeasurable hgi
  refine ⟨?_, ?_⟩
  · simpa only [smul_eq_mul, mul_one] using
      weightedExp_integral_hasFDerivAt_of_lt ν measurable_const.aestronglyMeasurable hgi hq
  · refine (hDgi ‖q‖ hq).mono' ?_ ?_
    · exact ((by fun_prop : Continuous (fun y : E => Real.exp ⟪q, y⟫)).aestronglyMeasurable).smul
        (weightedExpD_meas measurable_const.aestronglyMeasurable)
    · filter_upwards [] with y
      rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (real_inner_le_norm q y)) (norm_nonneg _)
/-- The local mixed first derivative, derived from the actual Euclidean graph norm moment. -/
 theorem solution {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) {r : ℝ} (_hr : 0 < r)
    (hexp : Integrable (fun y : EuclideanSpace ℝ (Option (Fin n)) => Real.exp (r * ‖y‖))
      (μ.map (fun x : EuclideanSpace ℝ (Fin n) =>
        (WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j :
          EuclideanSpace ℝ (Option (Fin n))))))
    (z : EuclideanSpace ℝ (Fin n)) (hz : ‖z‖ < r) :
    HasDerivAt (fun w : ℝ => Real.log (∫ x, Real.exp (w * f x + ⟪z, x⟫) ∂μ))
      (FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ f z) 0 := by
  let g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Option (Fin n)) :=
    fun x => WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j
  let Γ := μ.map g
  have hgm : Measurable g := by
    dsimp [g]
    apply (WithLp.measurable_toLp 2 _).comp
    rw [measurable_pi_iff]
    intro o
    cases o with
    | none => exact hf
    | some j => exact (measurable_pi_apply j).comp (WithLp.measurable_ofLp 2 _)
  let _ : IsProbabilityMeasure Γ := Measure.isProbabilityMeasure_map hgm.aemeasurable
  let q : EuclideanSpace ℝ (Option (Fin n)) :=
    WithLp.toLp 2 fun o => Option.elim o 0 fun j => z j
  let e0 : EuclideanSpace ℝ (Option (Fin n)) :=
    EuclideanSpace.basisFun (Option (Fin n)) ℝ none
  have hqnorm : ‖q‖ = ‖z‖ := by
    have hsq : ‖q‖ ^ 2 = ‖z‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_option]
      change (0 : ℝ) ^ 2 + ∑ j : Fin n, (z j) ^ 2 = ‖z‖ ^ 2
      rw [← EuclideanSpace.real_norm_sq_eq]
      norm_num
    nlinarith [norm_nonneg q, norm_nonneg z]
  have hq : ‖q‖ < r := hqnorm.trans_lt hz
  obtain ⟨hZ, hDint⟩ := FunctionalInequalities.KLS.LogConcave.Suspension.local_laplace_derivative_and_integrable Γ hexp hq
  let D : EuclideanSpace ℝ (Option (Fin n)) →L[ℝ] ℝ :=
    ∫ y, Real.exp ⟪q, y⟫ • FunctionalInequalities.Analysis.BakryEmery.weightedExpD (fun _ : EuclideanSpace ℝ (Option (Fin n)) => (1 : ℝ)) y ∂Γ
  have hinner (w : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
      ⟪w • e0 + q, g x⟫ = w * f x + ⟪z, x⟫ := by
    simp [g, q, e0, PiLp.inner_apply, Fintype.sum_option, mul_comm]
  have hmap (w : ℝ) :
      (∫ y, Real.exp ⟪w • e0 + q, y⟫ ∂Γ) = ∫ x, Real.exp (w * f x + ⟪z, x⟫) ∂μ := by
    dsimp [Γ]
    rw [integral_map hgm.aemeasurable
      ((by fun_prop : Continuous
        (fun y : EuclideanSpace ℝ (Option (Fin n)) => Real.exp ⟪w • e0 + q, y⟫)).aestronglyMeasurable)]
    simp_rw [hinner]
  have hNumΓ : Integrable (fun y => Real.exp ⟪q, y⟫ * y none) Γ := by
    have he := (ContinuousLinearMap.apply ℝ ℝ e0).integrable_comp hDint
    change Integrable (fun y => (Real.exp ⟪q, y⟫ •
      FunctionalInequalities.Analysis.BakryEmery.weightedExpD (fun _ : EuclideanSpace ℝ (Option (Fin n)) => (1 : ℝ)) y) e0) Γ at he
    simpa only [smul_apply, FunctionalInequalities.Analysis.BakryEmery.weightedExpD,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul, mul_one,
      e0, EuclideanSpace.inner_basisFun_real] using he
  have hDe0 : D e0 = ∫ x, Real.exp ⟪z, x⟫ * f x ∂μ := by
    dsimp [D]
    rw [ContinuousLinearMap.integral_apply hDint]
    simp only [smul_apply, FunctionalInequalities.Analysis.BakryEmery.weightedExpD,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul, mul_one,
      e0, EuclideanSpace.inner_basisFun_real]
    dsimp [Γ]
    rw [integral_map hgm.aemeasurable hNumΓ.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [] with x
    have hi : ⟪q, g x⟫ = ⟪z, x⟫ := by simpa using hinner 0 x
    rw [hi]
    rfl
  have hline : HasDerivAt (fun w : ℝ => w • e0 + q) e0 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e0).add_const q
  have hZline : HasDerivAt (fun w : ℝ => ∫ y, Real.exp ⟪w • e0 + q, y⟫ ∂Γ) (D e0) 0 := by
    have hZ' : HasFDerivAt (fun v => ∫ y, Real.exp ⟪v, y⟫ ∂Γ) D ((0 : ℝ) • e0 + q) := by
      simpa only [zero_smul, zero_add] using hZ
    exact hZ'.comp_hasDerivAt 0 hline
  have hQ : HasDerivAt (fun w : ℝ => ∫ x, Real.exp (w * f x + ⟪z, x⟫) ∂μ)
      (∫ x, Real.exp ⟪z, x⟫ * f x ∂μ) 0 := by
    simpa only [hmap, hDe0] using hZline
  have hZint : Integrable (fun y => Real.exp ⟪q, y⟫) Γ := by
    refine hexp.mono' ((by fun_prop : Continuous
      (fun y : EuclideanSpace ℝ (Option (Fin n)) => Real.exp ⟪q, y⟫)).aestronglyMeasurable) ?_
    filter_upwards [] with y
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr ((real_inner_le_norm q y).trans
      (mul_le_mul_of_nonneg_right hq.le (norm_nonneg y)))
  have hZpos : 0 < ∫ x, Real.exp ⟪z, x⟫ ∂μ := by
    have hp := integral_exp_pos hZint
    have heq : (∫ y, Real.exp ⟪q, y⟫ ∂Γ) = ∫ x, Real.exp ⟪z, x⟫ ∂μ := by
      simpa only [zero_smul, zero_add, zero_mul, zero_add] using hmap 0
    rwa [heq] at hp
  have htilt : FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ f z =
      (∫ x, Real.exp ⟪z, x⟫ * f x ∂μ) / (∫ x, Real.exp ⟪z, x⟫ ∂μ) := by
    rw [FunctionalInequalities.Analysis.BakryEmery.tiltAverage, FunctionalInequalities.Analysis.BakryEmery.expTilt, integral_tilted]
    simp only [smul_eq_mul, div_eq_mul_inv]
    rw [show (fun x => Real.exp ⟪z, x⟫ * (∫ y, Real.exp ⟪z, y⟫ ∂μ)⁻¹ * f x) =
      (fun x => (Real.exp ⟪z, x⟫ * f x) * (∫ y, Real.exp ⟪z, y⟫ ∂μ)⁻¹) by
        funext x; ring, integral_mul_const]
  simpa only [zero_mul, zero_add, ← htilt] using
    hQ.log (by simpa only [zero_mul, zero_add] using hZpos.ne')
