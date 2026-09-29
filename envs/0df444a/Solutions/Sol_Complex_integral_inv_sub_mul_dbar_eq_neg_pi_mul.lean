-- Prove2me | solution 1 for Complex.integral_inv_sub_mul_dbar_eq_neg_pi_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/6e5cc280-8707-599b-a51c-07a44c5904ea

import Mathlib
import Theorems.Thm_Complex_integral_mul_dbar_eq_zero_of_differentiableOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_integral_inv_sub_mul_dbar_eq_neg_pi_mul

open MeasureTheory Filter Complex Metric Set
open scoped Topology Real InnerProductSpace

namespace DbarFundamental

noncomputable def D (f : ℂ → ℂ) (z : ℂ) : ℂ := (fderiv ℝ f z 1 + I * fderiv ℝ f z I) / 2

noncomputable def φ (t : ℝ) : ℝ := Real.smoothTransition (2 - t)

theorem φ_contDiff : ContDiff ℝ 2 φ :=
  (Real.smoothTransition.contDiff (n := 2)).comp (contDiff_const.sub contDiff_id)

theorem φ_of_le_one {t : ℝ} (ht : t ≤ 1) : φ t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem φ_of_two_le {t : ℝ} (ht : 2 ≤ t) : φ t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem φ_differentiable : Differentiable ℝ φ := φ_contDiff.differentiable (by norm_num)

theorem deriv_φ_continuous : Continuous (deriv φ) := φ_contDiff.continuous_deriv (by norm_num)

theorem deriv_φ_of_two_lt {t : ℝ} (ht : 2 < t) : deriv φ t = 0 := by
  have : φ =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact φ_of_two_le (le_of_lt hs)
  rw [this.deriv_eq, deriv_const]

theorem deriv_φ_of_lt_one {t : ℝ} (ht : t < 1) : deriv φ t = 0 := by
  have : φ =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact φ_of_le_one (le_of_lt hs)
  rw [this.deriv_eq, deriv_const]

theorem exists_bound_deriv_φ : ∃ C, 0 ≤ C ∧ ∀ t, ‖deriv φ t‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 4)).exists_bound_of_continuousOn
    deriv_φ_continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc (0 : ℝ) 4
  · exact (hC t ht).trans (le_max_left _ _)
  · rw [mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with ht | ht
    · rw [deriv_φ_of_lt_one (by linarith)]; simp
    · rw [deriv_φ_of_two_lt (by linarith)]; simp

noncomputable def η (a : ℂ) (ε : ℝ) (z : ℂ) : ℂ := ((φ (‖z - a‖ ^ 2 / ε ^ 2) : ℝ) : ℂ)

variable (a : ℂ) {ε : ℝ}

theorem η_contDiff (ε : ℝ) : ContDiff ℝ 1 (η a ε) := by
  unfold η
  refine ofRealCLM.contDiff.comp ?_
  refine (φ_contDiff.of_le (by norm_num)).comp ?_
  exact ((contDiff_id.sub contDiff_const).norm_sq ℝ).div_const _

theorem η_eq_one (hε : 0 < ε) {z : ℂ} (hz : ‖z - a‖ ≤ ε) : η a ε z = 1 := by
  unfold η
  rw [φ_of_le_one, ofReal_one]
  rw [div_le_one (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) hz 2

theorem η_eq_zero (hε : 0 < ε) {z : ℂ} (hz : 2 * ε ≤ ‖z - a‖) : η a ε z = 0 := by
  unfold η
  rw [φ_of_two_le, ofReal_zero]
  rw [le_div_iff₀ (by positivity)]
  have h4 : (2 * ε) ^ 2 ≤ ‖z - a‖ ^ 2 := pow_le_pow_left₀ (by positivity) hz 2
  nlinarith

theorem η_hasCompactSupport (hε : 0 < ε) : HasCompactSupport (η a ε) := by
  refine HasCompactSupport.intro (isCompact_closedBall a (2 * ε)) fun z hz => ?_
  rw [mem_closedBall, dist_eq_norm, not_le] at hz
  exact η_eq_zero a hε hz.le

theorem hasFDerivAt_η (z : ℂ) :
    HasFDerivAt (η a ε) (ofRealCLM.comp ((deriv φ (‖z - a‖ ^ 2 / ε ^ 2) * (1 / ε ^ 2)) •
      ((2 : ℕ) • ((innerSL ℝ) (z - a)).comp (ContinuousLinearMap.id ℝ ℂ)))) z := by
  have hN : HasFDerivAt (fun w : ℂ => ‖w - a‖ ^ 2)
      ((2 : ℕ) • ((innerSL ℝ) (z - a)).comp (ContinuousLinearMap.id ℝ ℂ)) z :=
    ((hasFDerivAt_id z).sub_const a).norm_sq
  have hg : HasDerivAt (fun t : ℝ => φ (t / ε ^ 2))
      (deriv φ (‖z - a‖ ^ 2 / ε ^ 2) * (1 / ε ^ 2)) (‖z - a‖ ^ 2) := by
    have h1 : HasDerivAt (fun t : ℝ => t / ε ^ 2) (1 / ε ^ 2) (‖z - a‖ ^ 2) :=
      (hasDerivAt_id _).div_const _
    exact ((φ_differentiable _).hasDerivAt).comp _ h1
  have key := ofRealCLM.hasFDerivAt.comp z (hg.comp_hasFDerivAt z hN)
  exact key.congr_of_eventuallyEq (Eventually.of_forall fun w => by
    simp only [η, Function.comp_apply, ofRealCLM_apply])

theorem fderiv_η_apply (z v : ℂ) :
    fderiv ℝ (η a ε) z v =
      ((deriv φ (‖z - a‖ ^ 2 / ε ^ 2) / ε ^ 2 * (2 * ⟪z - a, v⟫_ℝ) : ℝ) : ℂ) := by
  rw [(hasFDerivAt_η a z).fderiv]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, two_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_id', id_eq,
    coe_innerSL_apply, smul_eq_mul, ofRealCLM_apply]
  push_cast
  ring

theorem D_η (z : ℂ) :
    D (η a ε) z = ((deriv φ (‖z - a‖ ^ 2 / ε ^ 2) / ε ^ 2 : ℝ) : ℂ) * (z - a) := by
  unfold D
  rw [fderiv_η_apply a, fderiv_η_apply a]
  have h1 : ⟪z - a, (1 : ℂ)⟫_ℝ = (z - a).re := by simp [Complex.inner]
  have h2 : ⟪z - a, I⟫_ℝ = (z - a).im := by simp [Complex.inner]; ring
  rw [h1, h2]
  push_cast
  linear_combination (((deriv φ (‖z - a‖ ^ 2 / ε ^ 2) : ℝ) : ℂ) / (ε : ℂ) ^ 2) * re_add_im (z - a)

theorem D_η_eq_zero (hε : 0 < ε) {z : ℂ} (hz : 2 * ε < ‖z - a‖) : D (η a ε) z = 0 := by
  rw [D_η a, deriv_φ_of_two_lt, zero_div, ofReal_zero, zero_mul]
  rw [lt_div_iff₀ (by positivity)]
  have h0 : 0 ≤ 2 * ε := by positivity
  have h4 : (2 * ε) ^ 2 < ‖z - a‖ ^ 2 := pow_lt_pow_left₀ hz h0 two_ne_zero
  nlinarith

theorem norm_D_η_le (hε : 0 < ε) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ t, ‖deriv φ t‖ ≤ C) (z : ℂ) :
    ‖D (η a ε) z‖ ≤ (2 * C / ε) * (closedBall a (2 * ε)).indicator (fun _ => (1 : ℝ)) z := by
  by_cases hz : z ∈ closedBall a (2 * ε)
  · rw [indicator_of_mem hz, mul_one, D_η a, norm_mul, Complex.norm_real, norm_div,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 2)]
    rw [mem_closedBall, dist_eq_norm] at hz
    calc ‖deriv φ (‖z - a‖ ^ 2 / ε ^ 2)‖ / ε ^ 2 * ‖z - a‖
        ≤ C / ε ^ 2 * (2 * ε) := by gcongr; exact hC _
      _ = 2 * C / ε := by field_simp
  · rw [indicator_of_notMem hz, mul_zero]
    rw [mem_closedBall, dist_eq_norm, not_le] at hz
    rw [D_η_eq_zero a hε hz, norm_zero]

theorem norm_η_le_one (ε : ℝ) (z : ℂ) : ‖η a ε z‖ ≤ 1 := by
  unfold η φ
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

theorem D_add {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    D (fun w => f w + g w) z = D f z + D g z := by
  unfold D
  rw [fderiv_fun_add hf hg]
  simp only [ContinuousLinearMap.add_apply]
  ring

theorem D_mul {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    D (fun w => f w * g w) z = f z * D g z + g z * D f z := by
  unfold D
  rw [fderiv_fun_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul]
  ring

theorem D_continuous {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) : Continuous (D f) := by
  unfold D
  have hc : ∀ v : ℂ, Continuous fun z => fderiv ℝ f z v := fun v =>
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  exact ((hc 1).add (continuous_const.mul (hc I))).div_const _

theorem D_eq_zero_of_notMem_tsupport {f : ℂ → ℂ} {z : ℂ} (hz : z ∉ tsupport f) : D f z = 0 := by
  simp [D, fderiv_of_notMem_tsupport ℝ hz]

theorem D_hasCompactSupport {f : ℂ → ℂ} (hf : HasCompactSupport f) : HasCompactSupport (D f) :=
  HasCompactSupport.intro hf fun _ hz => D_eq_zero_of_notMem_tsupport hz

theorem integrableOn_inv (r : ℝ) : IntegrableOn (fun x : ℂ => x⁻¹) (ball 0 r) := by
  have hd : 1 ≤ Module.finrank ℝ ℂ := by rw [Complex.finrank_real_complex]; norm_num
  refine integrableOn_ball_of_norm_le_rpow (μ := volume) hd (C := 1) (α := 1) ?_ ?_ ?_
  · rw [Complex.finrank_real_complex]; norm_num
  · refine Eventually.of_forall fun x => le_of_eq ?_
    rw [norm_inv, Real.rpow_neg_one, one_mul]
  · exact measurable_inv.aestronglyMeasurable

theorem integrableOn_inv_sub (r : ℝ) : IntegrableOn (fun z : ℂ => (z - a)⁻¹) (ball a r) := by
  have hT := (measurePreserving_add_right (volume : Measure ℂ) a).integrableOn_comp_preimage
    (measurableEmbedding_addRight a) (f := fun z : ℂ => (z - a)⁻¹) (s := ball a r)
  rw [← hT]
  have hpre : (fun x : ℂ => x + a) ⁻¹' ball a r = ball 0 r := by
    ext x
    simp only [mem_preimage, mem_ball_iff_norm, add_sub_cancel_right, sub_zero]
  rw [hpre]
  simp only [Function.comp_def, add_sub_cancel_right]
  exact integrableOn_inv r

theorem integrable_inv_sub_mul {u : ℂ → ℂ} (hu : Continuous u) (hus : HasCompactSupport u) :
    Integrable fun z => (z - a)⁻¹ * u z := by
  obtain ⟨R, hR⟩ := hus.isCompact.isBounded.subset_closedBall a
  have hq : IntegrableOn (fun z : ℂ => (z - a)⁻¹) (closedBall a (R + 1)) :=
    (integrableOn_inv_sub a (R + 2)).mono_set (closedBall_subset_ball (by linarith))
  have h1 : IntegrableOn (fun z => (z - a)⁻¹ * u z) (closedBall a (R + 1)) :=
    hq.mul_continuousOn hu.continuousOn (isCompact_closedBall _ _)
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 h1
  intro z hz
  have huz : u z ≠ 0 := fun h0 => hz (by simp [h0])
  exact closedBall_subset_closedBall (by linarith) (hR (subset_tsupport _ huz))

theorem integral_radial (f : ℝ → ℝ) : ∫ z : ℂ, f ‖z - a‖ = 2 * π * ∫ y in Ioi 0, y * f y := by
  have h1 := integral_sub_right_eq_self (μ := (volume : Measure ℂ)) (fun x : ℂ => f ‖x‖) a
  rw [h1, integral_fun_norm_addHaar]
  rw [Complex.finrank_real_complex, measureReal_def, Complex.volume_ball]
  simp [mul_assoc]

theorem integral_indicator_inv_norm {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ z : ℂ, (Iic ρ).indicator (fun y : ℝ => y⁻¹) ‖z - a‖ = 2 * π * ρ := by
  rw [integral_radial a ((Iic ρ).indicator fun y : ℝ => y⁻¹)]
  have h1 : ∫ y in Ioi (0 : ℝ), y * (Iic ρ).indicator (fun y : ℝ => y⁻¹) y
      = ∫ y in Ioi (0 : ℝ), (Iic ρ).indicator (fun _ => (1 : ℝ)) y := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    by_cases hyρ : y ∈ Iic ρ
    · rw [indicator_of_mem hyρ, indicator_of_mem hyρ, mul_inv_cancel₀ (ne_of_gt hy)]
    · rw [indicator_of_notMem hyρ, indicator_of_notMem hyρ, mul_zero]
  rw [h1, setIntegral_indicator measurableSet_Iic, setIntegral_const, Ioi_inter_Iic,
    Real.volume_real_Ioc_of_le hρ.le]
  simp

theorem integral_deriv_φ (hε : 0 < ε) :
    ∫ z : ℂ, deriv φ (‖z - a‖ ^ 2 / ε ^ 2) / ε ^ 2 = -π := by
  have h1 := integral_radial a (fun y => deriv φ (y ^ 2 / ε ^ 2) / ε ^ 2)
  rw [h1]

  have hderiv : ∀ y : ℝ, HasDerivAt (fun y : ℝ => φ (y ^ 2 / ε ^ 2) / 2)
      (y * (deriv φ (y ^ 2 / ε ^ 2) / ε ^ 2)) y := by
    intro y
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2 / ε ^ 2) (2 * y / ε ^ 2) y := by
      have := (hasDerivAt_pow 2 y).div_const (ε ^ 2)
      refine this.congr_deriv ?_
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    have h3 := (((φ_differentiable _).hasDerivAt).comp y h2).div_const 2
    refine h3.congr_deriv ?_
    ring
  have hzero : ∀ y : ℝ, 2 * ε ≤ |y| → deriv φ (y ^ 2 / ε ^ 2) = 0 := by
    intro y hy
    apply deriv_φ_of_two_lt
    rw [lt_div_iff₀ (by positivity)]
    have h0 : 0 ≤ 2 * ε := by positivity
    have h4 : (2 * ε) ^ 2 ≤ |y| ^ 2 := pow_le_pow_left₀ h0 hy 2
    have h5 : |y| ^ 2 = y ^ 2 := sq_abs y
    nlinarith
  have hcont : Continuous fun y : ℝ => y * (deriv φ (y ^ 2 / ε ^ 2) / ε ^ 2) :=
    continuous_id.mul ((deriv_φ_continuous.comp ((continuous_pow 2).div_const _)).div_const _)
  have hcs : HasCompactSupport fun y : ℝ => y * (deriv φ (y ^ 2 / ε ^ 2) / ε ^ 2) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -(2 * ε)) (b := 2 * ε)) fun y hy => ?_
    rw [mem_Icc, not_and_or, not_le, not_le] at hy
    have : 2 * ε ≤ |y| := by
      rcases hy with hy | hy
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [hzero y this]
    simp
  have htend : Tendsto (fun y : ℝ => φ (y ^ 2 / ε ^ 2) / 2) atTop (𝓝 0) := by
    refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
    filter_upwards [eventually_ge_atTop (2 * ε)] with y hy
    rw [φ_of_two_le, zero_div]
    rw [le_div_iff₀ (by positivity)]
    have h0 : 0 ≤ 2 * ε := by positivity
    have h4 : (2 * ε) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ h0 hy 2
    nlinarith
  have hΦc : Continuous fun y : ℝ => φ (y ^ 2 / ε ^ 2) / 2 :=
    (φ_differentiable.continuous.comp ((continuous_pow 2).div_const _)).div_const _
  have hI := integral_Ioi_of_hasDerivAt_of_tendsto (a := 0)
    hΦc.continuousWithinAt (fun y _ => hderiv y)
    (hcont.integrable_of_hasCompactSupport hcs).integrableOn htend
  rw [hI, φ_of_le_one (by norm_num)]
  ring

theorem integral_inv_sub_mul_D_η (hε : 0 < ε) : ∫ z, (z - a)⁻¹ * D (η a ε) z = -π := by
  have hae : (fun z => (z - a)⁻¹ * D (η a ε) z)
      =ᵐ[volume] fun z => ((deriv φ (‖z - a‖ ^ 2 / ε ^ 2) / ε ^ 2 : ℝ) : ℂ) := by
    filter_upwards [(Set.countable_singleton a).ae_notMem volume] with z hz
    rw [mem_singleton_iff] at hz
    rw [D_η a, mul_left_comm, inv_mul_cancel₀ (sub_ne_zero.2 hz), mul_one]
  rw [integral_congr_ae hae, integral_complex_ofReal, integral_deriv_φ a hε]
  push_cast
  ring

theorem main (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) :
    ∫ z, (z - a)⁻¹ * D h z = -π * h a := by

  obtain ⟨C, hC0, hC⟩ := exists_bound_deriv_φ
  obtain ⟨L, hL⟩ := hh.lipschitzWith_of_hasCompactSupport hsupp one_ne_zero
  obtain ⟨M, hM⟩ := (D_continuous hh).bounded_above_of_compact_support (D_hasCompactSupport hsupp)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a)
  have hhd : Differentiable ℝ h := hh.differentiable one_ne_zero

  have key : ∀ ε : ℝ, 0 < ε →
      ‖(∫ z, (z - a)⁻¹ * D h z) - (-π * h a)‖ ≤ (4 * π * M + 8 * π * L * C) * ε := by
    intro ε hε

    set e : ℂ → ℂ := η a ε with he_def
    have he1 : ContDiff ℝ 1 e := η_contDiff a ε
    have hed : Differentiable ℝ e := he1.differentiable one_ne_zero
    have hecs : HasCompactSupport e := η_hasCompactSupport a hε
    set k₁ : ℂ → ℂ := fun z => h z * e z with hk₁_def
    set k₂ : ℂ → ℂ := fun z => h z * (1 - e z) with hk₂_def
    have hk₁ : ContDiff ℝ 1 k₁ := hh.mul he1
    have hk₂ : ContDiff ℝ 1 k₂ := hh.mul (contDiff_const.sub he1)
    have hk₁cs : HasCompactSupport k₁ := hsupp.mul_right
    have hk₂cs : HasCompactSupport k₂ := hsupp.mul_right

    have hDsum : ∀ z, D h z = D k₁ z + D k₂ z := by
      intro z
      rw [← D_add (hk₁.differentiable one_ne_zero z) (hk₂.differentiable one_ne_zero z)]
      congr 1
      funext w
      simp only [hk₁_def, hk₂_def]
      ring
    have hDk₁ : ∀ z, D k₁ z = h z * D e z + e z * D h z := fun z => D_mul (hhd z) (hed z)

    have hI₁ : Integrable fun z => (z - a)⁻¹ * D k₁ z :=
      integrable_inv_sub_mul a (D_continuous hk₁) (D_hasCompactSupport hk₁cs)
    have hI₂ : Integrable fun z => (z - a)⁻¹ * D k₂ z :=
      integrable_inv_sub_mul a (D_continuous hk₂) (D_hasCompactSupport hk₂cs)
    have hI₃ : Integrable fun z => (z - a)⁻¹ * ((h z - h a) * D e z) :=
      integrable_inv_sub_mul a ((hh.continuous.sub continuous_const).mul (D_continuous he1))
        (D_hasCompactSupport hecs).mul_left
    have hI₄ : Integrable fun z => (z - a)⁻¹ * (e z * D h z) :=
      integrable_inv_sub_mul a (he1.continuous.mul (D_continuous hh))
        (D_hasCompactSupport hsupp).mul_left
    have hI₅ : Integrable fun z => (z - a)⁻¹ * D e z :=
      integrable_inv_sub_mul a (D_continuous he1) (D_hasCompactSupport hecs)

    have hfar : ∫ z, (z - a)⁻¹ * D k₂ z = 0 := by
      have hVo : IsOpen {z : ℂ | ε / 2 < ‖z - a‖} :=
        isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
      have hq : DifferentiableOn ℂ (fun z : ℂ => (z - a)⁻¹) {z : ℂ | ε / 2 < ‖z - a‖} := by
        intro z hz
        have hza : z - a ≠ 0 := by
          intro h0
          simp only [mem_setOf_eq, h0, norm_zero] at hz
          linarith
        exact ((differentiableAt_id.sub_const a).inv hza).differentiableWithinAt
      have hsub : tsupport k₂ ⊆ {z : ℂ | ε / 2 < ‖z - a‖} := by
        have hcl : IsClosed {z : ℂ | ε ≤ ‖z - a‖} :=
          isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
        refine (closure_minimal (fun z hz => ?_) hcl).trans fun z hz => ?_
        · rw [mem_setOf_eq]
          by_contra hlt
          push Not at hlt
          apply hz
          simp only [hk₂_def, he_def, η_eq_one a hε hlt.le, sub_self, mul_zero]
        · simp only [mem_setOf_eq] at hz ⊢
          linarith
      exact Complex.integral_mul_dbar_eq_zero_of_differentiableOn _ hVo _ hq k₂ hk₂ hk₂cs hsub

    have hmodel : ∫ z, (z - a)⁻¹ * D e z = -π := integral_inv_sub_mul_D_η a hε

    have hE₁ : ‖∫ z, (z - a)⁻¹ * (e z * D h z)‖ ≤ 4 * π * M * ε := by
      have hg : Integrable fun z : ℂ => M * (Iic (2 * ε)).indicator (fun y : ℝ => y⁻¹) ‖z - a‖ := by
        have h1 : Integrable ((closedBall a (2 * ε)).indicator fun z : ℂ => (z - a)⁻¹) :=
          ((integrableOn_inv_sub a (2 * ε + 1)).mono_set
            (closedBall_subset_ball (by linarith))).integrable_indicator measurableSet_closedBall
        refine (h1.norm.const_mul M).congr (Eventually.of_forall fun z => ?_)
        simp only [norm_indicator_eq_indicator_norm, norm_inv]
        congr 1
        by_cases hz : z ∈ closedBall a (2 * ε)
        · rw [indicator_of_mem hz, indicator_of_mem]
          rwa [mem_closedBall, dist_eq_norm] at hz
        · rw [indicator_of_notMem hz, indicator_of_notMem]
          rwa [mem_closedBall, dist_eq_norm] at hz
      calc ‖∫ z, (z - a)⁻¹ * (e z * D h z)‖
          ≤ ∫ z : ℂ, M * (Iic (2 * ε)).indicator (fun y : ℝ => y⁻¹) ‖z - a‖ := by
            refine norm_integral_le_of_norm_le hg (Eventually.of_forall fun z => ?_)
            by_cases hz : ‖z - a‖ ∈ Iic (2 * ε)
            · rw [indicator_of_mem hz, norm_mul, norm_mul, norm_inv, mul_comm M]
              gcongr
              calc ‖e z‖ * ‖D h z‖ ≤ 1 * M := by
                    gcongr
                    · exact norm_η_le_one a ε z
                    · exact hM z
                _ = M := one_mul M
            · rw [indicator_of_notMem hz, mul_zero]
              rw [mem_Iic, not_le] at hz
              rw [he_def, η_eq_zero a hε hz.le]
              simp
        _ = 4 * π * M * ε := by
            rw [integral_const_mul, integral_indicator_inv_norm a (by positivity)]
            ring

    have hE₂ : ‖∫ z, (z - a)⁻¹ * ((h z - h a) * D e z)‖ ≤ 8 * π * L * C * ε := by
      have hg : Integrable fun z : ℂ =>
          L * ((2 * C / ε) * (closedBall a (2 * ε)).indicator (fun _ => (1 : ℝ)) z) :=
        (((continuousOn_const.integrableOn_compact (isCompact_closedBall a (2 * ε))
          ).integrable_indicator measurableSet_closedBall).const_mul _).const_mul _
      calc ‖∫ z, (z - a)⁻¹ * ((h z - h a) * D e z)‖
          ≤ ∫ z : ℂ, L * ((2 * C / ε) * (closedBall a (2 * ε)).indicator (fun _ => (1 : ℝ)) z) := by
            refine norm_integral_le_of_norm_le hg (Eventually.of_forall fun z => ?_)
            have hqa : ‖(z - a)⁻¹‖ * ‖z - a‖ ≤ 1 := by
              rw [norm_inv]
              rcases eq_or_ne ‖z - a‖ 0 with h0 | h0
              · simp [h0]
              · rw [inv_mul_cancel₀ h0]
            calc ‖(z - a)⁻¹ * ((h z - h a) * D e z)‖
                = ‖(z - a)⁻¹‖ * (‖h z - h a‖ * ‖D e z‖) := by rw [norm_mul, norm_mul]
              _ ≤ ‖(z - a)⁻¹‖ * ((L * ‖z - a‖) * ‖D e z‖) := by
                  gcongr
                  exact hL.norm_sub_le z a
              _ = (‖(z - a)⁻¹‖ * ‖z - a‖) * (L * ‖D e z‖) := by ring
              _ ≤ 1 * (L * ‖D e z‖) := by gcongr
              _ ≤ L * ((2 * C / ε) * (closedBall a (2 * ε)).indicator (fun _ => (1 : ℝ)) z) := by
                  rw [one_mul]
                  gcongr
                  exact norm_D_η_le a hε hC0 hC z
        _ = 8 * π * L * C * ε := by
            rw [integral_const_mul, integral_const_mul,
              integral_indicator_const _ measurableSet_closedBall, measureReal_def,
              Complex.volume_closedBall]
            simp only [smul_eq_mul, mul_one]
            rw [ENNReal.toReal_mul, ← ENNReal.ofReal_pow (by positivity), ENNReal.toReal_ofReal
              (by positivity)]
            simp
            field_simp
            ring

    have hsplit : (∫ z, (z - a)⁻¹ * D h z) - (-π * h a)
        = (∫ z, (z - a)⁻¹ * (e z * D h z)) + ∫ z, (z - a)⁻¹ * ((h z - h a) * D e z) := by
      have h1 : ∫ z, (z - a)⁻¹ * D h z
          = (∫ z, (z - a)⁻¹ * D k₁ z) + ∫ z, (z - a)⁻¹ * D k₂ z := by
        rw [← integral_add hI₁ hI₂]
        congr 1
        funext z
        rw [hDsum z]
        ring
      have h2 : ∫ z, (z - a)⁻¹ * D k₁ z
          = (∫ z, (z - a)⁻¹ * ((h z - h a) * D e z)) + (h a * ∫ z, (z - a)⁻¹ * D e z)
            + ∫ z, (z - a)⁻¹ * (e z * D h z) := by
        have h3 : (fun z => (z - a)⁻¹ * D k₁ z) = fun z =>
            ((z - a)⁻¹ * ((h z - h a) * D e z) + h a * ((z - a)⁻¹ * D e z))
              + (z - a)⁻¹ * (e z * D h z) := by
          funext z
          rw [hDk₁ z]
          ring
        have hI₆ : Integrable fun z =>
            (z - a)⁻¹ * ((h z - h a) * D e z) + h a * ((z - a)⁻¹ * D e z) :=
          hI₃.add (hI₅.const_mul _)
        rw [h3, integral_add hI₆ hI₄, integral_add hI₃ (hI₅.const_mul _), integral_const_mul]
      rw [h1, hfar, add_zero, h2, hmodel]
      ring
    rw [hsplit]
    calc ‖(∫ z, (z - a)⁻¹ * (e z * D h z)) + ∫ z, (z - a)⁻¹ * ((h z - h a) * D e z)‖
        ≤ 4 * π * M * ε + 8 * π * L * C * ε := norm_add_le_of_le hE₁ hE₂
      _ = (4 * π * M + 8 * π * L * C) * ε := by ring

  set K : ℝ := 4 * π * M + 8 * π * L * C with hK
  have hK0 : 0 ≤ K := by positivity
  have h0 : ‖(∫ z, (z - a)⁻¹ * D h z) - (-π * h a)‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have := key (δ / (K + 1)) (by positivity)
    rw [zero_add]
    refine this.trans ?_
    rw [mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have := norm_le_zero_iff.1 h0
  exact sub_eq_zero.1 this

end DbarFundamental

open Complex MeasureTheory in
open scoped Real in
theorem solution
    (a : ℂ) (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) :
    ∫ z, (z - a)⁻¹ * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) = -π * h a :=
  DbarFundamental.main a h hh hsupp

end S_Complex_integral_inv_sub_mul_dbar_eq_neg_pi_mul
end P2MW
export P2MW.S_Complex_integral_inv_sub_mul_dbar_eq_neg_pi_mul (solution)
