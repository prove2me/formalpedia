-- Prove2me | solution 1 for CondMat0408017.unitarity_energy_conservation
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T17:22:33.017394+00:00
-- url     : https://prove2.me/submissions/4bbe776b-6562-4b15-8b92-0ba5c6436ea7

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex CondMat0408017

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (L1 ω c θ0 : ℝ) (hL1 : 0 < L1) (hω : 0 < ω) (hc : 0 < c)
    (hθ0 : θ0 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) (R : Ω → ℝ → ℂ)
    (hR : Measurable (Function.uncurry R))
    (h66 : ∀ᵐ w ∂P, 1 / L1 * ∫ q in (-(ω / c))..(ω / c),
        ‖sMatrixRad (ω / c) (ω / c * Real.sin θ0) (R w) q‖ ^ 2 / (2 * Real.pi) = 1) :
    ∫ θs in (-(Real.pi / 2))..(Real.pi / 2),
        meanDRC P L1 ω c θ0 θs (fun w => R w (ω / c * Real.sin θs)) = 1 := by
  have hwc : 0 < ω / c := div_pos hω hc
  have hcos0 : 0 < Real.cos θ0 := Real.cos_pos_of_mem_Ioo hθ0
  have hα0 : alpha0Rad (ω / c) (ω / c * Real.sin θ0) = (ω / c) * Real.cos θ0 := by
    simp only [alpha0Rad]
    have : (ω / c) ^ 2 - (ω / c * Real.sin θ0) ^ 2 = ((ω / c) * Real.cos θ0) ^ 2 := by
      have := Real.sin_sq_add_cos_sq θ0
      nlinarith
    rw [this, Real.sqrt_sq (mul_pos hwc hcos0).le]
  let φ : ℝ → ℝ := fun θ => (ω / c) * Real.sin θ
  let Iθ : Set ℝ := Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
  let Iq : Set ℝ := Set.Ioo (-(ω / c)) (ω / c)
  have hφ_inj : Set.InjOn φ Iθ := by
    intro a ha b hb hab
    have hsin : Real.sin a = Real.sin b := mul_left_cancel₀ hwc.ne' hab
    exact Real.injOn_sin (Set.Ioo_subset_Icc_self ha) (Set.Ioo_subset_Icc_self hb) hsin
  have hφ_img : φ '' Iθ = Iq := by
    ext q
    simp only [Set.mem_image, φ, Iθ, Iq, Set.mem_Ioo]
    constructor
    · rintro ⟨θ, ⟨h1, h2⟩, rfl⟩
      have hsin1 : -1 < Real.sin θ := by
        have hneg : Real.sin (-(Real.pi / 2)) = -1 := by rw [Real.sin_neg, Real.sin_pi_div_two]
        rw [← hneg]
        exact Real.strictMonoOn_sin (by constructor <;> linarith [Real.pi_pos])
          ⟨h1.le, h2.le⟩ h1
      have hsin2 : Real.sin θ < 1 := by
        rw [← Real.sin_pi_div_two]
        exact Real.strictMonoOn_sin ⟨h1.le, h2.le⟩
          (by constructor <;> linarith [Real.pi_pos]) h2
      constructor <;> nlinarith
    · rintro ⟨hq1, hq2⟩
      refine ⟨Real.arcsin (q / (ω / c)), ⟨?_, ?_⟩, ?_⟩
      · rw [← Real.arcsin_neg_one]
        exact Real.strictMonoOn_arcsin (by norm_num)
          ⟨by rw [le_div_iff₀ hwc]; linarith, by rw [div_le_iff₀ hwc]; linarith⟩
          (by rw [lt_div_iff₀ hwc]; linarith)
      · rw [← Real.arcsin_one]
        exact Real.strictMonoOn_arcsin
          ⟨by rw [le_div_iff₀ hwc]; linarith, by rw [div_le_iff₀ hwc]; linarith⟩
          (by norm_num) (by rw [div_lt_iff₀ hwc]; linarith)
      · rw [Real.sin_arcsin (by rw [le_div_iff₀ hwc]; linarith)
          (by rw [div_le_iff₀ hwc]; linarith)]
        exact mul_div_cancel₀ q hwc.ne'
  have hφ_deriv : ∀ θ ∈ Iθ, HasDerivWithinAt φ ((ω / c) * Real.cos θ) Iθ θ := fun θ _ =>
    ((Real.hasDerivAt_sin θ).const_mul (ω / c)).hasDerivWithinAt
  let F : Ω → ℝ → ℝ := fun w θs =>
    1 / L1 * (ω / (2 * Real.pi * c)) * (Real.cos θs ^ 2 / Real.cos θ0) * ‖R w (φ θs)‖ ^ 2
  have hF_meas : Measurable (fun p : Ω × ℝ => ENNReal.ofReal (F p.1 p.2)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    have hRφ : Measurable (fun p : Ω × ℝ => R p.1 (φ p.2)) :=
      hR.comp (measurable_fst.prodMk ((Real.continuous_sin.measurable.const_mul (ω / c)).comp measurable_snd))
    have hC : Measurable (fun p : Ω × ℝ =>
        1 / L1 * (ω / (2 * Real.pi * c)) * (Real.cos p.2 ^ 2 / Real.cos θ0)) := by
      have hc2 : Continuous (fun θ : ℝ =>
          1 / L1 * (ω / (2 * Real.pi * c)) * (Real.cos θ ^ 2 / Real.cos θ0)) := by fun_prop
      exact hc2.measurable.comp measurable_snd
    exact hC.mul (hRφ.norm.pow_const 2)
  have hlint_ae : ∀ᵐ w ∂P, ∫⁻ θs in Iθ, ENNReal.ofReal (F w θs) = 1 := by
    filter_upwards [h66] with w hw
    have hle : -(ω / c) ≤ ω / c := by linarith
    have hint_eq : ∫ q in (-(ω / c))..(ω / c),
        ‖sMatrixRad (ω / c) (ω / c * Real.sin θ0) (R w) q‖ ^ 2 / (2 * Real.pi) =
        ∫ q in Iq, ‖sMatrixRad (ω / c) (ω / c * Real.sin θ0) (R w) q‖ ^ 2 / (2 * Real.pi) := by
      rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [hint_eq] at hw
    have hw' : ∫ q in Iq,
        1 / L1 * (‖sMatrixRad (ω / c) (ω / c * Real.sin θ0) (R w) q‖ ^ 2 / (2 * Real.pi)) = 1 := by
      rw [integral_const_mul]; exact hw
    have hInt : IntegrableOn (fun q =>
        1 / L1 * (‖sMatrixRad (ω / c) (ω / c * Real.sin θ0) (R w) q‖ ^ 2 / (2 * Real.pi))) Iq volume := by
      by_contra hni
      have := integral_undef hni
      rw [this] at hw'
      norm_num at hw'
    have hnn : 0 ≤ᵐ[volume.restrict Iq] fun q =>
        1 / L1 * (‖sMatrixRad (ω / c) (ω / c * Real.sin θ0) (R w) q‖ ^ 2 / (2 * Real.pi)) :=
      Filter.Eventually.of_forall (fun q => by positivity)
    have hlint_q : ∫⁻ q in Iq, ENNReal.ofReal
        (1 / L1 * (‖sMatrixRad (ω / c) (ω / c * Real.sin θ0) (R w) q‖ ^ 2 / (2 * Real.pi))) = 1 := by
      rw [← ofReal_integral_eq_lintegral_ofReal hInt hnn, hw', ENNReal.ofReal_one]
    rw [← hφ_img] at hlint_q
    rw [MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hφ_deriv hφ_inj] at hlint_q
    rw [← hlint_q]
    refine setLIntegral_congr_fun measurableSet_Ioo (fun θs hθs => ?_)
    have hcos : 0 < Real.cos θs := Real.cos_pos_of_mem_Ioo hθs
    have hαs : alpha0Rad (ω / c) (φ θs) = (ω / c) * Real.cos θs := by
      simp only [alpha0Rad, φ]
      have : (ω / c) ^ 2 - (ω / c * Real.sin θs) ^ 2 = ((ω / c) * Real.cos θs) ^ 2 := by
        have := Real.sin_sq_add_cos_sq θs
        nlinarith
      rw [this, Real.sqrt_sq (mul_pos hwc hcos).le]
    rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (mul_pos hwc hcos)]
    congr 1
    simp only [F, sMatrixRad, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, hαs, hα0]
    have hratio : 0 ≤ (ω / c * Real.cos θs) / (ω / c * Real.cos θ0) := by positivity
    rw [Real.sq_sqrt hratio]
    field_simp [hL1.ne', hω.ne', hc.ne', Real.pi_ne_zero, hcos0.ne']
  have htonelli : ∫⁻ θs in Iθ, (∫⁻ w, ENNReal.ofReal (F w θs) ∂P) = 1 := by
    rw [← MeasureTheory.lintegral_lintegral_swap hF_meas.aemeasurable]
    calc ∫⁻ w, (∫⁻ θs in Iθ, ENNReal.ofReal (F w θs)) ∂P
        = ∫⁻ _w, (1 : ENNReal) ∂P := lintegral_congr_ae hlint_ae
      _ = 1 := by simp
  have hae_fin : ∀ᵐ θs ∂(volume.restrict Iθ), (∫⁻ w, ENNReal.ofReal (F w θs) ∂P) ≠ ⊤ :=
    ae_lt_top (hF_meas.lintegral_prod_left') (by rw [htonelli]; exact ENNReal.one_ne_top) |>.mono
      (fun _ h => h.ne)
  have hmean_ae : ∀ᵐ θs ∂(volume.restrict Iθ),
      ENNReal.ofReal (meanDRC P L1 ω c θ0 θs (fun w => R w (φ θs))) =
        ∫⁻ w, ENNReal.ofReal (F w θs) ∂P := by
    filter_upwards [hae_fin] with θs hfin
    have hF_w_meas : Measurable (fun w => F w θs) := by
      have hRφ : Measurable (fun w => R w (φ θs)) :=
        hR.comp (measurable_id.prodMk measurable_const)
      exact measurable_const.mul (hRφ.norm.pow_const 2)
    have hF_w_nn : 0 ≤ᵐ[P] fun w => F w θs := Filter.Eventually.of_forall (fun w => by
      simp only [F]; positivity)
    have hF_w_int : Integrable (fun w => F w θs) P := by
      refine ⟨hF_w_meas.aestronglyMeasurable, ?_⟩
      rw [HasFiniteIntegral]
      have : (fun w => ‖F w θs‖ₑ) = fun w => ENNReal.ofReal (F w θs) := by
        ext w
        rw [Real.enorm_eq_ofReal (by simp only [F]; positivity)]
      rw [this]
      exact lt_top_iff_ne_top.mpr hfin
    rw [← ofReal_integral_eq_lintegral_ofReal hF_w_int hF_w_nn]
    congr 1
    simp only [meanDRC, F, integral_const_mul]
  have hmean_lint : ∫⁻ θs in Iθ, ENNReal.ofReal (meanDRC P L1 ω c θ0 θs (fun w => R w (φ θs))) = 1 := by
    rw [lintegral_congr_ae hmean_ae, htonelli]
  have hmean_meas : AEStronglyMeasurable (fun θs => meanDRC P L1 ω c θ0 θs (fun w => R w (φ θs)))
      (volume.restrict Iθ) := by
    have h1 : Measurable (fun θs => ∫⁻ w, ENNReal.ofReal (F w θs) ∂P) :=
      hF_meas.lintegral_prod_left'
    have h2 : AEStronglyMeasurable (fun θs => (∫⁻ w, ENNReal.ofReal (F w θs) ∂P).toReal)
        (volume.restrict Iθ) := (ENNReal.measurable_toReal.comp h1).aestronglyMeasurable
    refine h2.congr ?_
    filter_upwards [hmean_ae] with θs hθs
    rw [← hθs, ENNReal.toReal_ofReal]
    simp only [meanDRC]
    have hint_nn : 0 ≤ ∫ w, ‖R w (φ θs)‖ ^ 2 ∂P :=
      integral_nonneg (fun w => sq_nonneg _)
    positivity
  have hmean_nn : 0 ≤ᵐ[volume.restrict Iθ] fun θs => meanDRC P L1 ω c θ0 θs (fun w => R w (φ θs)) := by
    filter_upwards with θs
    simp only [meanDRC]
    have hint_nn : 0 ≤ ∫ w, ‖R w (φ θs)‖ ^ 2 ∂P :=
      integral_nonneg (fun w => sq_nonneg _)
    positivity
  have hmean_int : IntegrableOn (fun θs => meanDRC P L1 ω c θ0 θs (fun w => R w (φ θs))) Iθ volume := by
    refine ⟨hmean_meas, ?_⟩
    rw [HasFiniteIntegral]
    have hcongr : (fun θs => ‖meanDRC P L1 ω c θ0 θs (fun w => R w (φ θs))‖ₑ) =ᵐ[volume.restrict Iθ]
        fun θs => ENNReal.ofReal (meanDRC P L1 ω c θ0 θs (fun w => R w (φ θs))) := by
      filter_upwards [hmean_nn] with θs hnn
      exact Real.enorm_eq_ofReal hnn
    rw [lintegral_congr_ae hcongr, hmean_lint]
    exact ENNReal.one_lt_top
  have hpi : -(Real.pi / 2) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  rw [intervalIntegral.integral_of_le hpi, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have := ofReal_integral_eq_lintegral_ofReal hmean_int hmean_nn
  rw [hmean_lint] at this
  have hge0 : 0 ≤ ∫ θs in Iθ, meanDRC P L1 ω c θ0 θs (fun w => R w (φ θs)) :=
    integral_nonneg_of_ae hmean_nn
  have := congrArg ENNReal.toReal this
  simpa [ENNReal.toReal_ofReal hge0] using this
