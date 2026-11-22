-- Prove2me | solution 1 for ExplicitFormula.complex_log_fourier_finite_part
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:54:52.733001+00:00
-- url     : https://prove2.me/submissions/ea4dc31c-3ff2-491f-a913-2e229b05278a

import Mathlib
import Theorems.Thm_FamousTheorems_frullani_integral

open Filter Topology
open scoped Real ContDiff

set_option autoImplicit false

namespace Sol_ExplicitFormula_complex_log_fourier_finite_part

open MeasureTheory Set
open scoped FourierTransform

/-- `∫₀^∞ log u · e^{-u} du = -γ`. -/
lemma integral_log_mul_exp_neg :
    ∫ u in Ioi (0:ℝ), Real.log u * Real.exp (-u) = -Real.eulerMascheroniConstant := by
  have h1 : (0:ℝ) < (1:ℂ).re := by simp
  have hd := Complex.hasDerivAt_GammaIntegral h1
  have hd' : HasDerivAt Complex.Gamma
      (∫ t : ℝ in Ioi 0, (t:ℂ) ^ ((1:ℂ) - 1) * (Real.log t * Real.exp (-t))) ((1:ℝ):ℂ) := by
    have : Complex.Gamma =ᶠ[𝓝 (1:ℂ)] Complex.GammaIntegral := by
      have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
      filter_upwards [hopen.mem_nhds (by simp : (1:ℂ) ∈ {s : ℂ | 0 < s.re})] with s hs
      exact Complex.Gamma_eq_integral hs
    simpa using hd.congr_of_eventuallyEq this
  have hr := hd'.real_of_complex
  have hr' : HasDerivAt Real.Gamma
      ((∫ t : ℝ in Ioi 0, (t:ℂ) ^ ((1:ℂ) - 1) * (Real.log t * Real.exp (-t)))).re 1 := by
    convert hr using 1
    funext x; rfl
  have huniq := hr'.unique Real.hasDerivAt_Gamma_one
  have hint : (∫ t : ℝ in Ioi 0, (t:ℂ) ^ ((1:ℂ) - 1) * (Real.log t * Real.exp (-t))) =
      ((∫ t : ℝ in Ioi 0, Real.log t * Real.exp (-t) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp
  rw [hint, Complex.ofReal_re] at huniq
  exact huniq

lemma integrableOn_log_mul_exp_neg :
    IntegrableOn (fun u : ℝ => Real.log u * Real.exp (-u)) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_log_mul_exp_neg]
  have := Real.one_half_lt_eulerMascheroniConstant
  linarith

/-- `∫₀^∞ r log(r²) e^{-π r²} dr = -(γ + log π)/(2π)`. -/
lemma integral_r_log_sq_gauss :
    ∫ r in Ioi (0:ℝ), r * Real.log (r ^ 2) * Real.exp (-π * r ^ 2) =
      -(Real.eulerMascheroniConstant + Real.log π) / (2 * π) := by
  -- substitution y = r^2
  have hsub := integral_comp_rpow_Ioi (fun y : ℝ => Real.log y * Real.exp (-π * y) / 2)
    (p := 2) (by norm_num)
  have h1 : ∫ r in Ioi (0:ℝ), r * Real.log (r ^ 2) * Real.exp (-π * r ^ 2) =
      ∫ y in Ioi (0:ℝ), Real.log y * Real.exp (-π * y) / 2 := by
    rw [← hsub]
    refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    have hr0 : (0:ℝ) < r := hr
    simp only [smul_eq_mul]
    have e1 : r ^ ((2:ℝ) - 1) = r := by norm_num
    have e2 : r ^ (2:ℝ) = r ^ 2 := by norm_num
    rw [e1, e2]
    norm_num
    ring
  -- scaling y = u / π
  have hscale := integral_comp_mul_left_Ioi
    (fun u : ℝ => (Real.log u - Real.log π) * Real.exp (-u) / 2) 0 Real.pi_pos
  have h2 : ∫ y in Ioi (0:ℝ), Real.log y * Real.exp (-π * y) / 2 =
      π⁻¹ * ∫ u in Ioi (0:ℝ), (Real.log u - Real.log π) * Real.exp (-u) / 2 := by
    rw [mul_zero] at hscale
    rw [← smul_eq_mul, ← hscale]
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy0 : (0:ℝ) < y := hy
    rw [Real.log_mul Real.pi_pos.ne' hy0.ne']
    ring_nf
  have h3 : ∫ u in Ioi (0:ℝ), (Real.log u - Real.log π) * Real.exp (-u) / 2 =
      (-Real.eulerMascheroniConstant - Real.log π) / 2 := by
    have hA := integrableOn_log_mul_exp_neg
    have hB : IntegrableOn (fun u : ℝ => Real.log π * Real.exp (-u)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have : (fun u : ℝ => (Real.log u - Real.log π) * Real.exp (-u) / 2) =
        fun u => (Real.log u * Real.exp (-u) - Real.log π * Real.exp (-u)) / 2 := by
      ext u; ring
    rw [this, integral_div, integral_sub hA hB, integral_log_mul_exp_neg, integral_const_mul,
      integral_exp_neg_Ioi_zero]
    ring
  rw [h1, h2, h3]
  field_simp
  ring

lemma integrableOn_r_log_sq_gauss :
    IntegrableOn (fun r : ℝ => r * Real.log (r ^ 2) * Real.exp (-π * r ^ 2)) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_r_log_sq_gauss]
  have := Real.one_half_lt_eulerMascheroniConstant
  have : 0 < Real.log π := Real.log_pos (by linarith [Real.pi_gt_three])
  have : 0 < π := Real.pi_pos
  apply div_ne_zero
  · linarith
  · positivity

lemma tendsto_setIntegral_of_ae_eventually_mem {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {S : ι → Set α}
    (hS : ∀ i, MeasurableSet (S i)) {φ : α → E} (hφ : Integrable φ μ)
    (h : ∀ᵐ x ∂μ, ∀ᶠ i in l, x ∈ S i) :
    Tendsto (fun i => ∫ x in S i, φ x ∂μ) l (𝓝 (∫ x, φ x ∂μ)) := by
  simp_rw [← integral_indicator (hS _)]
  refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖φ x‖)
    (Eventually.of_forall fun i => hφ.aestronglyMeasurable.indicator (hS i))
    (Eventually.of_forall fun i => ae_of_all _ fun x => norm_indicator_le_norm_self _ _)
    hφ.norm ?_
  filter_upwards [h] with x hx
  exact tendsto_const_nhds.congr' (hx.mono fun i hi => (indicator_of_mem hi _).symm)

lemma tendsto_setIntegral_Ioi_zero {φ : ℝ → ℝ} (hφ : IntegrableOn φ (Ioi 0)) :
    Tendsto (fun δ : ℝ => ∫ r in Ioi δ, φ r) (𝓝[>] 0) (𝓝 (∫ r in Ioi (0:ℝ), φ r)) := by
  have h := tendsto_setIntegral_of_ae_eventually_mem (μ := volume.restrict (Ioi (0:ℝ)))
    (l := 𝓝[>] (0:ℝ)) (S := fun δ => Ioi δ) (fun δ => measurableSet_Ioi) hφ ?_
  · refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [Measure.restrict_restrict measurableSet_Ioi,
      Set.inter_eq_left.mpr (Ioi_subset_Ioi (le_of_lt hδ))]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (eventually_lt_nhds hx).filter_mono nhdsWithin_le_nhds

lemma ibp_E1 {δ : ℝ} (hδ : 0 < δ) :
    ∫ r in Ioi δ, Real.exp (-π * r ^ 2) / r =
      -(Real.log δ * Real.exp (-π * δ ^ 2)) +
        ∫ r in Ioi δ, π * (r * Real.log (r ^ 2) * Real.exp (-π * r ^ 2)) := by
  have hu : ∀ x ∈ Ioi δ, HasDerivAt Real.log (x⁻¹) x := fun x hx =>
    Real.hasDerivAt_log (ne_of_gt (lt_trans hδ hx))
  have hv : ∀ x ∈ Ioi δ, HasDerivAt (fun x : ℝ => Real.exp (-π * x ^ 2))
      (Real.exp (-π * x ^ 2) * (-π * (2 * x))) x := by
    intro x _
    have := ((hasDerivAt_pow 2 x).const_mul (-π)).exp
    convert this using 1
    simp
  have hint0 := integrableOn_r_log_sq_gauss
  have huv' : IntegrableOn (Real.log * fun x : ℝ => Real.exp (-π * x ^ 2) * (-π * (2 * x)))
      (Ioi δ) := by
    have : IntegrableOn (fun x : ℝ => -π * (x * Real.log (x ^ 2) * Real.exp (-π * x ^ 2)))
        (Ioi δ) := (hint0.mono_set (Ioi_subset_Ioi hδ.le)).const_mul (-π)
    refine IntegrableOn.congr_fun this (fun x hx => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply]
    rw [Real.log_pow]
    push_cast
    ring
  have hu'v : IntegrableOn ((fun x : ℝ => x⁻¹) * fun x : ℝ => Real.exp (-π * x ^ 2)) (Ioi δ) := by
    have hg : Integrable (fun x : ℝ => Real.exp (-π * x ^ 2)) := integrable_exp_neg_mul_sq Real.pi_pos
    refine Integrable.mono' ((hg.integrableOn).const_mul δ⁻¹) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      intro x hx
      have hx0 : x ≠ 0 := ne_of_gt (lt_trans hδ hx)
      exact ((continuousAt_inv₀ hx0).mul (by fun_prop)).continuousWithinAt
    · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => ?_)
      have hx0 : 0 < x := lt_trans hδ hx
      simp only [Pi.mul_apply, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      gcongr
      exact le_of_lt hx
  have h_zero : Tendsto (Real.log * fun x : ℝ => Real.exp (-π * x ^ 2)) (𝓝[>] δ)
      (𝓝 (Real.log δ * Real.exp (-π * δ ^ 2))) := by
    have : ContinuousAt (Real.log * fun x : ℝ => Real.exp (-π * x ^ 2)) δ :=
      (Real.continuousAt_log hδ.ne').mul (by fun_prop)
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  have h_infty : Tendsto (Real.log * fun x : ℝ => Real.exp (-π * x ^ 2)) atTop (𝓝 0) := by
    have hlim := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
      simp only [Pi.mul_apply]
      exact mul_nonneg (Real.log_nonneg hx) (Real.exp_pos _).le
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
      simp only [Pi.mul_apply, pow_one]
      have hlog : Real.log x ≤ x := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
      have hexp : Real.exp (-π * x ^ 2) ≤ Real.exp (-x) := by
        apply Real.exp_le_exp.mpr
        have : x ≤ π * x ^ 2 := by
          have h3 := Real.pi_gt_three
          nlinarith
        linarith
      exact mul_le_mul hlog hexp (Real.exp_pos _).le (by linarith)
  have key := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h_zero h_infty
  have e1 : ∫ r in Ioi δ, Real.exp (-π * r ^ 2) / r =
      ∫ r in Ioi δ, (r⁻¹ * Real.exp (-π * r ^ 2)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
    ring
  have e2 : ∫ r in Ioi δ, π * (r * Real.log (r ^ 2) * Real.exp (-π * r ^ 2)) =
      -∫ r in Ioi δ, Real.log r * (Real.exp (-π * r ^ 2) * (-π * (2 * r))) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
    rw [Real.log_pow]
    push_cast
    ring
  rw [e1, e2]
  linarith

lemma tendsto_E1 :
    Tendsto (fun δ : ℝ => (∫ r in Ioi δ, Real.exp (-π * r ^ 2) / r) + Real.log δ) (𝓝[>] 0)
      (𝓝 (-(Real.eulerMascheroniConstant + Real.log π) / 2)) := by
  have hA : Tendsto (fun δ : ℝ => Real.log δ * (1 - Real.exp (-π * δ ^ 2))) (𝓝[>] 0) (𝓝 0) := by
    have hl := ((tendsto_log_mul_rpow_nhdsGT_zero (r := 2) (by norm_num)).abs).const_mul π
    rw [abs_zero, mul_zero] at hl
    refine squeeze_zero_norm' ?_ hl
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ0 : (0:ℝ) < δ := hδ
    rw [Real.norm_eq_abs, abs_mul, Real.rpow_two, abs_mul (Real.log δ)]
    have h1 : |1 - Real.exp (-π * δ ^ 2)| ≤ π * δ ^ 2 := by
      have hle : Real.exp (-π * δ ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by
        have : 0 ≤ π * δ ^ 2 := by positivity
        linarith)
      rw [abs_of_nonneg (by linarith)]
      have := Real.add_one_le_exp (-π * δ ^ 2)
      linarith
    have h2 : |δ ^ 2| = δ ^ 2 := abs_of_nonneg (by positivity)
    rw [h2]
    calc |Real.log δ| * |1 - Real.exp (-π * δ ^ 2)| ≤ |Real.log δ| * (π * δ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = π * (|Real.log δ| * δ ^ 2) := by ring
  have hB : Tendsto (fun δ : ℝ => ∫ r in Ioi δ, π * (r * Real.log (r ^ 2) * Real.exp (-π * r ^ 2)))
      (𝓝[>] 0) (𝓝 (∫ r in Ioi (0:ℝ), π * (r * Real.log (r ^ 2) * Real.exp (-π * r ^ 2)))) :=
    tendsto_setIntegral_Ioi_zero (integrableOn_r_log_sq_gauss.const_mul π)
  have hval : ∫ r in Ioi (0:ℝ), π * (r * Real.log (r ^ 2) * Real.exp (-π * r ^ 2)) =
      -(Real.eulerMascheroniConstant + Real.log π) / 2 := by
    rw [integral_const_mul, integral_r_log_sq_gauss]
    field_simp
  rw [hval] at hB
  have := hA.add hB
  rw [zero_add] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [ibp_E1 hδ]
  ring



lemma radial_integral (φ : ℝ → ℂ) :
    ∫ z : ℂ, φ ‖z‖ = 2 * (π:ℂ) * ∫ r in Ioi (0:ℝ), (r:ℂ) * φ r := by
  rw [integral_fun_norm_addHaar volume φ]
  simp [Complex.finrank_real_complex, Measure.real, Complex.volume_ball]
  ring

lemma radial_integrable (φ : ℝ → ℂ) :
    Integrable (fun z : ℂ => φ ‖z‖) ↔ IntegrableOn (fun r : ℝ => (r:ℂ) * φ r) (Ioi 0) := by
  rw [integrable_fun_norm_addHaar volume]
  simp [Complex.finrank_real_complex]

lemma integral_log_gauss :
    ∫ w : ℂ, (Real.log (‖w‖ ^ 2) : ℂ) * Complex.exp (-(π:ℂ) * (‖w‖:ℂ) ^ 2) =
      -((Real.eulerMascheroniConstant + Real.log π : ℝ) : ℂ) := by
  have h := radial_integral (fun r => (Real.log (r ^ 2) : ℂ) * Complex.exp (-(π:ℂ) * (r:ℂ) ^ 2))
  beta_reduce at h
  rw [h]
  have e : ∫ r in Ioi (0:ℝ), (r:ℂ) * ((Real.log (r ^ 2) : ℂ) * Complex.exp (-(π:ℂ) * (r:ℂ) ^ 2)) =
      ∫ r in Ioi (0:ℝ), ((r * Real.log (r ^ 2) * Real.exp (-π * r ^ 2) : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
    push_cast
    ring
  rw [e, integral_complex_ofReal, integral_r_log_sq_gauss]
  have : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

lemma setIntegral_gauss_div {δ : ℝ} (hδ : 0 < δ) :
    ∫ z in {z : ℂ | δ ≤ ‖z‖}, Complex.exp (-(π:ℂ) * (‖z‖:ℂ) ^ 2) / ((‖z‖ ^ 2 : ℝ) : ℂ) =
      2 * (π:ℂ) * ((∫ r in Ioi δ, Real.exp (-π * r ^ 2) / r : ℝ) : ℂ) := by
  have hS : MeasurableSet {z : ℂ | δ ≤ ‖z‖} := measurableSet_le measurable_const measurable_norm
  rw [← integral_indicator hS]
  have e1 : ({z : ℂ | δ ≤ ‖z‖}.indicator
      fun z => Complex.exp (-(π:ℂ) * (‖z‖:ℂ) ^ 2) / ((‖z‖ ^ 2 : ℝ) : ℂ)) =
      fun z => (Ici δ).indicator
        (fun r : ℝ => Complex.exp (-(π:ℂ) * (r:ℂ) ^ 2) / ((r ^ 2 : ℝ) : ℂ)) ‖z‖ := by
    ext z
    by_cases hz : δ ≤ ‖z‖
    · rw [indicator_of_mem (show z ∈ {z : ℂ | δ ≤ ‖z‖} from hz),
        indicator_of_mem (show ‖z‖ ∈ Ici δ from hz)]
    · rw [indicator_of_notMem (show z ∉ {z : ℂ | δ ≤ ‖z‖} from hz),
        indicator_of_notMem (show ‖z‖ ∉ Ici δ from hz)]
  rw [e1, radial_integral]
  congr 1
  rw [← integral_complex_ofReal]
  have e2 : ∀ r ∈ Ioi (0:ℝ), (r:ℂ) * (Ici δ).indicator
      (fun r : ℝ => Complex.exp (-(π:ℂ) * (r:ℂ) ^ 2) / ((r ^ 2 : ℝ) : ℂ)) r =
      (Ici δ).indicator (fun r : ℝ => ((Real.exp (-π * r ^ 2) / r : ℝ) : ℂ)) r := by
    intro r hr
    have hr0 : (r:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
    by_cases h : r ∈ Ici δ
    · rw [indicator_of_mem h, indicator_of_mem h]
      push_cast
      field_simp
    · rw [indicator_of_notMem h, indicator_of_notMem h, mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi e2, setIntegral_indicator measurableSet_Ici,
    inter_eq_right.mpr (Ici_subset_Ioi.mpr hδ), integral_Ici_eq_integral_Ioi]



lemma parseval {h g : ℂ → ℂ} (hh : Integrable h) (hg : Integrable g) :
    ∫ w, 𝓕 h w * g w = ∫ z, h z * 𝓕 g z := by
  have := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
    (L := innerₗ ℂ) (e := Real.fourierChar) Real.continuous_fourierChar continuous_inner hh hg
  simp only [smul_eq_mul] at this
  have e1 : ∀ z, VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℂ).flip g z = 𝓕 g z := by
    intro z
    rw [Real.fourier_eq]
    simp only [VectorFourier.fourierIntegral, LinearMap.flip_apply]
    congr 1
    ext v
    rw [innerₗ_apply_apply, real_inner_comm]
  simp_rw [e1] at this
  exact this

lemma integral_fourier_eq {φ : ℂ → ℂ} (hφ : Integrable φ) (hF : Integrable (𝓕 φ))
    (hc : ContinuousAt φ 0) : ∫ w, 𝓕 φ w = φ 0 := by
  have := hφ.fourierInv_fourier_eq hF hc
  rw [Real.fourierInv_eq] at this
  simpa using this

lemma fourier_gauss {t : ℝ} (ht : 0 < t) (w : ℂ) :
    𝓕 (fun v : ℂ => Complex.exp (-((π * t : ℝ) : ℂ) * (‖v‖:ℂ) ^ 2)) w =
      ((t⁻¹ : ℝ) : ℂ) * Complex.exp (-((π / t : ℝ) : ℂ) * (‖w‖:ℂ) ^ 2) := by
  have hb : 0 < (((π * t : ℝ)) : ℂ).re := by simp; positivity
  rw [fourier_gaussian_innerProductSpace hb]
  simp [Complex.finrank_real_complex]
  have hπ : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have ht' : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  congr 1
  · field_simp
  · congr 1
    field_simp

lemma integrable_gauss {t : ℝ} (ht : 0 < t) :
    Integrable (fun w : ℂ => Complex.exp (-((π * t : ℝ) : ℂ) * (‖w‖:ℂ) ^ 2)) := by
  have hb : 0 < (((π * t : ℝ)) : ℂ).re := by simp; positivity
  simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb 0 (0:ℂ)

lemma abs_exp_neg_sub_exp_neg_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-x) - Real.exp (-y)| ≤ |x - y| := by
  wlog hxy : x ≤ y generalizing x y
  · rw [abs_sub_comm, abs_sub_comm x]; exact this hy hx (le_of_not_ge hxy)
  have h1 : Real.exp (-y) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
  rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
  have h2 : Real.exp (-y) = Real.exp (-x) * Real.exp (-(y - x)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 := Real.add_one_le_exp (-(y - x))
  have h4 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h5 : Real.exp (-(y - x)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [h2]
  nlinarith [Real.exp_pos (-x)]

lemma frullani_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => x⁻¹ • (Real.exp (-(π * x)) - Real.exp (-(π * a * x)))) (Ioi 0) := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => x⁻¹ • (Real.exp (-(π * x)) - Real.exp (-(π * a * x)))) volume :=
    (by fun_prop : Measurable
      (fun x : ℝ => x⁻¹ • (Real.exp (-(π * x)) - Real.exp (-(π * a * x))))).aestronglyMeasurable
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · refine Integrable.mono' (g := fun _ => π * |1 - a|) (integrableOn_const (by simp)) hmeas.restrict ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => ?_)
    have hx0 : 0 < x := hx.1
    rw [smul_eq_mul, norm_mul, norm_inv, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx0]
    have := abs_exp_neg_sub_exp_neg_le (x := π * x) (y := π * a * x) (by positivity) (by positivity)
    have e : |π * x - π * a * x| = x * (π * |1 - a|) := by
      rw [show π * x - π * a * x = (π * x) * (1 - a) by ring, abs_mul, abs_of_pos (by positivity)]
      ring
    rw [e] at this
    rw [inv_mul_le_iff₀ hx0]
    exact this
  · have i1 := exp_neg_integrableOn_Ioi 1 Real.pi_pos
    have i2 := exp_neg_integrableOn_Ioi 1 (mul_pos Real.pi_pos ha)
    refine Integrable.mono' (i1.add i2) hmeas.restrict ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => ?_)
    have hx1 : 1 < x := hx
    have hx0 : 0 < x := by linarith
    rw [smul_eq_mul, norm_mul, norm_inv, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx0]
    have hinv : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx1.le
    have hb : |Real.exp (-(π * x)) - Real.exp (-(π * a * x))| ≤
        Real.exp (-π * x) + Real.exp (-(π * a) * x) := by
      rw [neg_mul, neg_mul]
      refine (abs_sub _ _).trans (le_of_eq ?_)
      rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    calc x⁻¹ * |Real.exp (-(π * x)) - Real.exp (-(π * a * x))|
        ≤ 1 * (Real.exp (-π * x) + Real.exp (-(π * a) * x)) :=
          mul_le_mul hinv hb (abs_nonneg _) zero_le_one
      _ = _ := by simp

lemma frullani_value {a : ℝ} (ha : 0 < a) :
    ∫ x in Ioi (0:ℝ), x⁻¹ • (Real.exp (-(π * x)) - Real.exp (-(π * a * x))) = Real.log a := by
  have hf : LocallyIntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi 0) :=
    (Continuous.locallyIntegrable (by fun_prop)).locallyIntegrableOn _
  have hL : Tendsto (fun x : ℝ => Real.exp (-x)) (𝓝[>] 0) (𝓝 1) := by
    have := ((by fun_prop : Continuous fun x : ℝ => Real.exp (-x)).tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have hR : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
  have := FamousTheorems.frullani_integral (f := fun x : ℝ => Real.exp (-x)) (a := π) (b := π * a)
    (L := 1) (R := 0) hf Real.pi_pos (by positivity) hL hR (frullani_integrable ha)
  rw [this, mul_div_cancel_left₀ _ Real.pi_ne_zero]
  simp

lemma frullani_abs {a : ℝ} (ha : 0 < a) :
    ∫ x in Ioi (0:ℝ), ‖x⁻¹ • (Real.exp (-(π * x)) - Real.exp (-(π * a * x)))‖ = |Real.log a| := by
  rcases le_or_gt 1 a with h1 | h1
  · rw [abs_of_nonneg (Real.log_nonneg h1), ← frullani_value ha]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx0 : 0 < x := hx
    refine Real.norm_of_nonneg (smul_nonneg (inv_nonneg.mpr hx0.le) ?_)
    have : Real.exp (-(π * a * x)) ≤ Real.exp (-(π * x)) := by
      apply Real.exp_le_exp.mpr
      have : π * x ≤ π * a * x := by
        have := mul_le_mul_of_nonneg_left h1 (le_of_lt (mul_pos Real.pi_pos hx0))
        nlinarith
      linarith
    linarith
  · rw [abs_of_neg (Real.log_neg ha h1), ← frullani_value ha, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx0 : 0 < x := hx
    refine Real.norm_of_nonpos ?_
    rw [smul_eq_mul]
    refine mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hx0.le) ?_
    have : Real.exp (-(π * x)) ≤ Real.exp (-(π * a * x)) := by
      apply Real.exp_le_exp.mpr
      have : π * a * x ≤ π * x := by
        have := mul_le_mul_of_nonneg_left h1.le (le_of_lt (mul_pos Real.pi_pos hx0))
        nlinarith
      linarith
    linarith

lemma inv_sq_exp {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => (x ^ 2)⁻¹ * Real.exp (-(c / x))) (Ioi 0) ∧
      ∫ x in Ioi (0:ℝ), (x ^ 2)⁻¹ * Real.exp (-(c / x)) = c⁻¹ := by
  have hp : (-1:ℝ) ≠ 0 := by norm_num
  have e : ∀ x ∈ Ioi (0:ℝ), (|(-1:ℝ)| * x ^ ((-1:ℝ) - 1)) • Real.exp (-c * x ^ (-1:ℝ)) =
      (x ^ 2)⁻¹ * Real.exp (-(c / x)) := by
    intro x hx
    have hx0 : 0 < x := hx
    rw [smul_eq_mul, Real.rpow_neg_one, show (-1:ℝ) - 1 = -2 by norm_num,
      Real.rpow_neg hx0.le, Real.rpow_two]
    simp [div_eq_mul_inv]
  have hg : IntegrableOn (fun y : ℝ => Real.exp (-c * y)) (Ioi 0) := exp_neg_integrableOn_Ioi 0 hc
  constructor
  · have := (integrableOn_Ioi_comp_rpow_iff (fun y : ℝ => Real.exp (-c * y)) hp).mpr hg
    exact this.congr_fun e measurableSet_Ioi
  · rw [← setIntegral_congr_fun measurableSet_Ioi e,
      integral_comp_rpow_Ioi (fun y : ℝ => Real.exp (-c * y)) hp,
      integral_exp_mul_Ioi (by linarith) 0]
    simp

theorem h_identity (h : ℂ → ℂ) (hh : Integrable h) (hFh : Integrable (𝓕 h))
    (h0 : ∫ w, 𝓕 h w = 0)
    (hA : Integrable (fun z => h z / ((‖z‖ ^ 2 : ℝ) : ℂ)))
    (hB : Integrable (fun w => (Real.log (‖w‖ ^ 2) : ℂ) * 𝓕 h w)) :
    ∫ z, h z / ((‖z‖ ^ 2 : ℝ) : ℂ) = -(π:ℂ) * ∫ w, (Real.log (‖w‖ ^ 2) : ℂ) * 𝓕 h w := by
  have hne : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := by simp [ae_iff]
  let k : ℂ → ℝ → ℂ := fun w x =>
    ((x⁻¹ • (Real.exp (-(π * x)) - Real.exp (-(π * ‖w‖ ^ 2 * x))) : ℝ) : ℂ) * 𝓕 h w
  -- Step 1: Frullani
  have step1 : ∫ w, (Real.log (‖w‖ ^ 2) : ℂ) * 𝓕 h w = ∫ w, ∫ x in Ioi (0:ℝ), k w x := by
    refine integral_congr_ae ?_
    filter_upwards [hne] with w hw
    have ha : 0 < ‖w‖ ^ 2 := by positivity
    simp only [k]
    rw [integral_mul_const, integral_complex_ofReal, frullani_value ha]
  -- Step 2: Fubini
  have hk_int : Integrable (Function.uncurry k) (volume.prod (volume.restrict (Ioi (0:ℝ)))) := by
    have hmeas : AEStronglyMeasurable (Function.uncurry k)
        (volume.prod (volume.restrict (Ioi (0:ℝ)))) := by
      have m1 : Measurable (fun p : ℂ × ℝ =>
          ((p.2⁻¹ • (Real.exp (-(π * p.2)) - Real.exp (-(π * ‖p.1‖ ^ 2 * p.2))) : ℝ) : ℂ)) := by
        fun_prop
      exact m1.aestronglyMeasurable.mul hFh.aestronglyMeasurable.comp_fst
    refine (integrable_prod_iff hmeas).mpr ⟨?_, ?_⟩
    · filter_upwards [hne] with w hw
      have ha : 0 < ‖w‖ ^ 2 := by positivity
      show Integrable (fun x => k w x) _
      exact ((frullani_integrable ha).ofReal).mul_const _
    · refine (hB.norm).congr ?_
      filter_upwards [hne] with w hw
      have ha : 0 < ‖w‖ ^ 2 := by positivity
      simp only [Function.uncurry, k, norm_mul, Complex.norm_real]
      rw [integral_mul_const, frullani_abs ha, Real.norm_eq_abs]
  have step2 := integral_integral_swap hk_int
  -- Step 3: Parseval with Gaussians
  have step3 : ∀ x ∈ Ioi (0:ℝ), ∫ w, k w x =
      -(∫ z, ((((x ^ 2)⁻¹ * Real.exp (-(π * ‖z‖ ^ 2 / x))) : ℝ) : ℂ) * h z) := by
    intro x hx
    have hx0 : (0:ℝ) < x := hx
    have hG := integrable_gauss hx0
    have hpars := parseval hh hG
    simp_rw [fourier_gauss hx0] at hpars
    have e : ∀ w, k w x = ((x⁻¹:ℝ):ℂ) * ((Real.exp (-(π*x)) : ℂ) * 𝓕 h w -
        𝓕 h w * Complex.exp (-((π * x : ℝ) : ℂ) * (‖w‖:ℂ) ^ 2)) := by
      intro w
      simp only [k, smul_eq_mul]
      push_cast
      ring_nf
    have hFG : Integrable (fun w => 𝓕 h w * Complex.exp (-((π * x : ℝ) : ℂ) * (‖w‖:ℂ) ^ 2)) := by
      refine hFh.norm.mono' (hFh.aestronglyMeasurable.mul hG.aestronglyMeasurable) ?_
      refine ae_of_all _ (fun w => ?_)
      rw [norm_mul]
      have : ‖Complex.exp (-((π * x : ℝ) : ℂ) * (‖w‖:ℂ) ^ 2)‖ ≤ 1 := by
        rw [Complex.norm_exp]
        apply Real.exp_le_one_iff.mpr
        have : (-((π * x : ℝ) : ℂ) * (‖w‖:ℂ) ^ 2).re = -(π * x * ‖w‖ ^ 2) := by
          rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]
          ring
        rw [this]
        have : 0 ≤ π * x * ‖w‖ ^ 2 := by positivity
        linarith
      calc ‖𝓕 h w‖ * ‖Complex.exp (-((π * x : ℝ) : ℂ) * (‖w‖:ℂ) ^ 2)‖ ≤ ‖𝓕 h w‖ * 1 :=
            mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ = ‖𝓕 h w‖ := mul_one _
    simp_rw [e]
    rw [integral_const_mul, integral_sub (hFh.const_mul _) hFG, integral_const_mul, h0, hpars]
    have e2 : ∀ z, ((((x ^ 2)⁻¹ * Real.exp (-(π * ‖z‖ ^ 2 / x))) : ℝ) : ℂ) * h z =
        ((x⁻¹:ℝ):ℂ) * (h z * (((x⁻¹ : ℝ) : ℂ) * Complex.exp (-((π / x : ℝ) : ℂ) * (‖z‖:ℂ) ^ 2))) := by
      intro z
      push_cast
      ring_nf
    simp_rw [e2]
    rw [integral_const_mul]
    ring
  -- Step 4: second Fubini
  let m : ℂ → ℝ → ℂ := fun z x => ((((x ^ 2)⁻¹ * Real.exp (-(π * ‖z‖ ^ 2 / x))) : ℝ) : ℂ) * h z
  have hm_int : Integrable (Function.uncurry m) (volume.prod (volume.restrict (Ioi (0:ℝ)))) := by
    have hmeas : AEStronglyMeasurable (Function.uncurry m)
        (volume.prod (volume.restrict (Ioi (0:ℝ)))) := by
      have m1 : Measurable (fun p : ℂ × ℝ =>
          ((((p.2 ^ 2)⁻¹ * Real.exp (-(π * ‖p.1‖ ^ 2 / p.2))) : ℝ) : ℂ)) := by
        fun_prop
      exact m1.aestronglyMeasurable.mul hh.aestronglyMeasurable.comp_fst
    refine (integrable_prod_iff hmeas).mpr ⟨?_, ?_⟩
    · filter_upwards [hne] with z hz
      have hc : 0 < π * ‖z‖ ^ 2 := by positivity
      show Integrable (fun x => m z x) _
      exact ((inv_sq_exp hc).1.ofReal).mul_const _
    · refine ((hA.norm).const_mul π⁻¹).congr ?_
      filter_upwards [hne] with z hz
      have hc : 0 < π * ‖z‖ ^ 2 := by positivity
      simp only [Function.uncurry, m, norm_mul, Complex.norm_real]
      have e3 : ∀ x ∈ Ioi (0:ℝ), ‖(x ^ 2)⁻¹‖ * ‖Real.exp (-(π * ‖z‖ ^ 2 / x))‖ * ‖h z‖ =
          ((x ^ 2)⁻¹ * Real.exp (-(π * ‖z‖ ^ 2 / x))) * ‖h z‖ := by
        intro x hx
        rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
      rw [setIntegral_congr_fun measurableSet_Ioi e3, integral_mul_const, (inv_sq_exp hc).2,
        norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      field_simp
  have step4 : ∫ x in Ioi (0:ℝ), ∫ z, m z x = ∫ z, ∫ x in Ioi (0:ℝ), m z x :=
    (integral_integral_swap hm_int).symm
  have step5 : ∫ z, ∫ x in Ioi (0:ℝ), m z x = (π⁻¹ : ℂ) * ∫ z, h z / ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hne] with z hz
    have hc : 0 < π * ‖z‖ ^ 2 := by positivity
    simp only [m]
    rw [integral_mul_const, integral_complex_ofReal, (inv_sq_exp hc).2]
    push_cast
    field_simp
  have hpi : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [step1, step2, setIntegral_congr_fun measurableSet_Ioi step3, integral_neg, step4, step5]
  field_simp



lemma integrableOn_inv_norm_ball :
    IntegrableOn (fun z : ℂ => ‖z‖⁻¹) (Metric.ball (0:ℂ) 1) := by
  refine (integrableOn_fun_norm_addHaar (μ := volume) (E := ℂ) (f := fun y : ℝ => y⁻¹)
    (r := 1)).mpr ?_
  simp only [Complex.finrank_real_complex]
  refine (integrableOn_const (C := (1:ℝ)) (by simp)).congr_fun (fun y hy => ?_) measurableSet_Ioo
  have hy0 : y ≠ 0 := ne_of_gt hy.1
  simp [hy0]

lemma integrable_inv_norm_indicator (C : ℝ) :
    Integrable (fun z : ℂ => C * (Metric.ball (0:ℂ) 1).indicator (fun z : ℂ => ‖z‖⁻¹) z) :=
  ((integrableOn_inv_norm_ball).integrable_indicator Metric.isOpen_ball.measurableSet).const_mul C

lemma abs_log_le (r : ℝ) (hr : 0 < r) : |Real.log r| ≤ (if r < 1 then r⁻¹ else r) := by
  split_ifs with h
  · rw [abs_of_neg (Real.log_neg hr h), ← Real.log_inv]
    have := Real.log_le_sub_one_of_pos (inv_pos.mpr hr)
    linarith
  · have h := not_lt.mp h
    rw [abs_of_nonneg (Real.log_nonneg h)]
    have := Real.log_le_sub_one_of_pos hr
    linarith

lemma integrable_log_mul {ψ : ℂ → ℂ} (hψ : Integrable ψ) {C : ℝ} (hC : ∀ w, ‖ψ w‖ ≤ C)
    (hψ1 : Integrable (fun w => ‖w‖ * ‖ψ w‖)) :
    Integrable (fun w => (Real.log (‖w‖ ^ 2) : ℂ) * ψ w) := by
  refine Integrable.mono' ((((integrable_inv_norm_indicator C).add hψ.norm).add hψ1).const_mul 2)
    (((by fun_prop : Measurable fun w : ℂ => (Real.log (‖w‖ ^ 2) : ℂ)).aestronglyMeasurable).mul
      hψ.aestronglyMeasurable) (ae_of_all _ (fun w => ?_))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC w)
  have hind : 0 ≤ (Metric.ball (0:ℂ) 1).indicator (fun z : ℂ => ‖z‖⁻¹) w :=
    indicator_nonneg (fun z _ => inv_nonneg.mpr (norm_nonneg z)) w
  simp only [Pi.add_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rcases eq_or_ne w 0 with hw | hw
  · subst hw
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Real.log_zero,
      abs_zero, zero_mul]
    have := norm_nonneg (ψ 0)
    positivity
  have hr : 0 < ‖w‖ := norm_pos_iff.mpr hw
  rw [Real.log_pow, Nat.cast_ofNat, abs_mul, abs_two]
  have hl := abs_log_le ‖w‖ hr
  have hψn := norm_nonneg (ψ w)
  split_ifs at hl with h1
  · have hmem : w ∈ Metric.ball (0:ℂ) 1 := by simpa using h1
    rw [indicator_of_mem hmem]
    have : |Real.log ‖w‖| * ‖ψ w‖ ≤ C * ‖w‖⁻¹ :=
      calc |Real.log ‖w‖| * ‖ψ w‖ ≤ ‖w‖⁻¹ * C := mul_le_mul hl (hC w) hψn (by positivity)
        _ = C * ‖w‖⁻¹ := mul_comm _ _
    nlinarith [mul_nonneg (norm_nonneg w) hψn]
  · have : |Real.log ‖w‖| * ‖ψ w‖ ≤ ‖w‖ * ‖ψ w‖ := mul_le_mul_of_nonneg_right hl hψn
    nlinarith [mul_nonneg hC0 hind]

lemma integrable_div_norm_sq {φ : ℂ → ℂ} (hφ : Integrable φ) {L : ℝ}
    (hL : ∀ z : ℂ, ‖z‖ < 1 → ‖φ z‖ ≤ L * ‖z‖) :
    Integrable (fun z => φ z / ((‖z‖ ^ 2 : ℝ) : ℂ)) := by
  have hmeas : AEStronglyMeasurable (fun z => φ z / ((‖z‖ ^ 2 : ℝ) : ℂ)) volume :=
    (hφ.aestronglyMeasurable.aemeasurable.div
      (by fun_prop : Measurable fun z : ℂ => ((‖z‖ ^ 2 : ℝ) : ℂ)).aemeasurable).aestronglyMeasurable
  refine Integrable.mono' ((integrable_inv_norm_indicator L).add hφ.norm) hmeas
    (ae_of_all _ (fun z => ?_))
  simp only [Pi.add_apply]
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hφn := norm_nonneg (φ z)
  rcases eq_or_ne z 0 with hz | hz
  · subst hz
    simp
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  by_cases h1 : ‖z‖ < 1
  · have hmem : z ∈ Metric.ball (0:ℂ) 1 := by simpa using h1
    rw [indicator_of_mem hmem]
    have := hL z h1
    rw [div_le_iff₀ (by positivity)]
    have e : (L * ‖z‖⁻¹ + ‖φ z‖) * ‖z‖ ^ 2 = L * ‖z‖ + ‖φ z‖ * ‖z‖ ^ 2 := by
      field_simp
    rw [e]
    nlinarith [mul_nonneg hφn (sq_nonneg ‖z‖)]
  · have hmem : z ∉ Metric.ball (0:ℂ) 1 := by simpa using h1
    rw [indicator_of_notMem hmem, mul_zero, zero_add]
    have h1 := not_lt.mp h1
    rw [div_le_iff₀ (by positivity)]
    have h2 : 1 ≤ ‖z‖ ^ 2 := one_le_pow₀ h1
    nlinarith [mul_le_mul_of_nonneg_left h2 hφn]

lemma schwartz_lip (f : SchwartzMap ℂ ℂ) : ∃ L : ℝ, ∀ z : ℂ, ‖f z - f 0‖ ≤ L * ‖z‖ := by
  obtain ⟨C, _, hC⟩ := f.decay 0 1
  refine ⟨C, fun z => ?_⟩
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := fun x => f x) (s := univ)
    (fun x _ => f.differentiableAt) (fun x _ => by
      have := hC x
      rw [pow_zero, one_mul, norm_iteratedFDeriv_one] at this
      exact this) convex_univ (mem_univ 0) (mem_univ z)
  simpa using this

lemma schwartz_bdd (f : SchwartzMap ℂ ℂ) : ∃ C : ℝ, ∀ z : ℂ, ‖f z‖ ≤ C := by
  obtain ⟨C, _, hC⟩ := f.decay 0 0
  refine ⟨C, fun z => ?_⟩
  have := hC z
  rwa [pow_zero, one_mul, norm_iteratedFDeriv_zero] at this


theorem main (f : SchwartzMap ℂ ℂ) :
    Tendsto
      (fun δ : ℝ => (∫ z in {z : ℂ | δ ≤ ‖z‖}, f z / ((‖z‖ ^ 2 : ℝ) : ℂ)) +
        2 * π * f 0 * (Real.log δ : ℂ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (-(π : ℂ) * (∫ w : ℂ, (Real.log (‖w‖ ^ 2) : ℂ) *
          FourierTransform.fourier (f : ℂ → ℂ) w) -
        2 * π * ((Real.eulerMascheroniConstant + Real.log π : ℝ) : ℂ) * f 0)) := by
  obtain ⟨G, hGdef⟩ : ∃ G : ℂ → ℂ, G = fun z => Complex.exp (-(π:ℂ) * (‖z‖:ℂ) ^ 2) := ⟨_, rfl⟩
  have hpi : (π:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hG_int : Integrable G := by
    have := integrable_gauss (t := 1) one_pos
    rw [hGdef]
    simpa using this
  have hFG : 𝓕 G = G := by
    ext w
    have := fourier_gauss (t := 1) one_pos w
    rw [hGdef]
    simpa using this
  have hGint1 : ∫ z, G z = 1 := by
    have := GaussianFourier.integral_cexp_neg_mul_sq_norm (V := ℂ) (b := (π:ℂ))
      (by simp [Real.pi_pos])
    rw [hGdef]
    simp only [Complex.finrank_real_complex] at this
    rw [this, div_self hpi]
    simp
  have hGreal : ∀ z, G z = ((Real.exp (-π * ‖z‖ ^ 2) : ℝ) : ℂ) := by
    intro z; rw [hGdef]; push_cast; ring_nf
  obtain ⟨h, hhdef⟩ : ∃ h : ℂ → ℂ, h = fun z => f z - f 0 * G z := ⟨_, rfl⟩
  have hf_int : Integrable (f : ℂ → ℂ) := f.integrable
  have hh_int : Integrable h := by
    rw [hhdef]; exact hf_int.sub (hG_int.const_mul _)
  have hFf_int : Integrable (𝓕 (f : ℂ → ℂ)) := (𝓕 f).integrable
  have hFh : ∀ w, 𝓕 h w = 𝓕 (f : ℂ → ℂ) w - f 0 * G w := by
    intro w
    have i1 := (Real.fourierIntegral_convergent_iff (μ := volume) (f := (f : ℂ → ℂ)) w).mpr hf_int
    have i2 := (Real.fourierIntegral_convergent_iff (μ := volume) (f := fun z => f 0 * G z) w).mpr
      (hG_int.const_mul _)
    calc 𝓕 h w = 𝓕 (f : ℂ → ℂ) w - f 0 * 𝓕 G w := by
          rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq, hhdef]
          simp only [smul_sub]
          rw [integral_sub i1 i2, ← integral_const_mul]
          congr 1
          congr 1
          ext v
          rw [mul_smul_comm]
      _ = _ := by rw [hFG]
  have hFh' : 𝓕 h = fun w => 𝓕 (f : ℂ → ℂ) w - f 0 * G w := funext hFh
  have hFh_int : Integrable (𝓕 h) := by
    rw [hFh']; exact hFf_int.sub (hG_int.const_mul _)
  have h0 : ∫ w, 𝓕 h w = 0 := by
    rw [hFh', integral_sub hFf_int (hG_int.const_mul _), integral_const_mul, hGint1,
      integral_fourier_eq hf_int hFf_int f.continuous.continuousAt]
    ring
  -- integrability of h / |z|^2
  obtain ⟨Lf, hLf⟩ := schwartz_lip f
  have hA : Integrable (fun z => h z / ((‖z‖ ^ 2 : ℝ) : ℂ)) := by
    refine integrable_div_norm_sq hh_int (L := Lf + ‖f 0‖ * π) (fun z hz => ?_)
    have hz0 := norm_nonneg z
    have hG1 : ‖1 - G z‖ ≤ π * ‖z‖ := by
      rw [hGreal, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have hle : Real.exp (-π * ‖z‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by
        have : 0 ≤ π * ‖z‖ ^ 2 := by positivity
        linarith)
      rw [abs_of_nonneg (by linarith)]
      have := Real.add_one_le_exp (-π * ‖z‖ ^ 2)
      have : ‖z‖ ^ 2 ≤ ‖z‖ := by nlinarith
      have := Real.pi_pos
      nlinarith
    have e : h z = (f z - f 0) + f 0 * (1 - G z) := by rw [hhdef]; ring
    rw [e]
    calc ‖(f z - f 0) + f 0 * (1 - G z)‖ ≤ ‖f z - f 0‖ + ‖f 0‖ * ‖1 - G z‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul]
      _ ≤ Lf * ‖z‖ + ‖f 0‖ * (π * ‖z‖) := by
          gcongr
          exact hLf z
      _ = (Lf + ‖f 0‖ * π) * ‖z‖ := by ring
  -- integrability of log * Fourier transforms
  obtain ⟨CF, hCF⟩ := schwartz_bdd (𝓕 f)
  have hBf : Integrable (fun w => (Real.log (‖w‖ ^ 2) : ℂ) * 𝓕 (f : ℂ → ℂ) w) := by
    refine integrable_log_mul hFf_int (C := CF) (fun w => hCF w) ?_
    have := (𝓕 f).integrable_pow_mul volume 1
    simp only [pow_one, SchwartzMap.fourier_coe] at this
    exact this
  have hK : ∫ w, (Real.log (‖w‖ ^ 2) : ℂ) * G w =
      -((Real.eulerMascheroniConstant + Real.log π : ℝ) : ℂ) := by
    rw [hGdef]; exact integral_log_gauss
  have hBG : Integrable (fun w => (Real.log (‖w‖ ^ 2) : ℂ) * G w) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [hK, neg_ne_zero, Complex.ofReal_ne_zero]
    have := Real.one_half_lt_eulerMascheroniConstant
    have : 0 < Real.log π := Real.log_pos (by linarith [Real.pi_gt_three])
    linarith
  have hB : Integrable (fun w => (Real.log (‖w‖ ^ 2) : ℂ) * 𝓕 h w) := by
    have := hBf.sub (hBG.const_mul (f 0))
    refine this.congr (ae_of_all _ (fun w => ?_))
    simp only [Pi.sub_apply]
    rw [hFh]
    ring
  have hId := h_identity h hh_int hFh_int h0 hA hB
  have hlogsplit : ∫ w, (Real.log (‖w‖ ^ 2) : ℂ) * 𝓕 h w =
      (∫ w, (Real.log (‖w‖ ^ 2) : ℂ) * 𝓕 (f : ℂ → ℂ) w) - f 0 * ∫ w, (Real.log (‖w‖ ^ 2) : ℂ) * G w := by
    rw [← integral_const_mul, ← integral_sub hBf (hBG.const_mul _)]
    congr 1
    ext w
    rw [hFh]
    ring
  -- the set integrals
  have hS : ∀ δ : ℝ, MeasurableSet {z : ℂ | δ ≤ ‖z‖} :=
    fun δ => measurableSet_le measurable_const measurable_norm
  have hsetint : ∀ {φ : ℂ → ℂ}, Integrable φ → ∀ δ : ℝ, 0 < δ →
      IntegrableOn (fun z => φ z / ((‖z‖ ^ 2 : ℝ) : ℂ)) {z : ℂ | δ ≤ ‖z‖} := by
    intro φ hφ δ hδ
    have hmeas : AEStronglyMeasurable (fun z => φ z / ((‖z‖ ^ 2 : ℝ) : ℂ)) volume :=
      (hφ.aestronglyMeasurable.aemeasurable.div
        (by fun_prop : Measurable fun z : ℂ => ((‖z‖ ^ 2 : ℝ) : ℂ)).aemeasurable).aestronglyMeasurable
    refine Integrable.mono' ((hφ.norm.const_mul (δ ^ 2)⁻¹).integrableOn) hmeas.restrict ?_
    refine ae_restrict_of_forall_mem (hS δ) (fun z hz => ?_)
    have hz' : δ ≤ ‖z‖ := hz
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity), div_eq_inv_mul]
    gcongr
  have hdec : ∀ δ : ℝ, 0 < δ →
      (∫ z in {z : ℂ | δ ≤ ‖z‖}, f z / ((‖z‖ ^ 2 : ℝ) : ℂ)) + 2 * π * f 0 * (Real.log δ : ℂ) =
      (∫ z in {z : ℂ | δ ≤ ‖z‖}, h z / ((‖z‖ ^ 2 : ℝ) : ℂ)) +
        f 0 * ((∫ z in {z : ℂ | δ ≤ ‖z‖}, G z / ((‖z‖ ^ 2 : ℝ) : ℂ)) +
          2 * π * (Real.log δ : ℂ)) := by
    intro δ hδ
    have e : ∀ z, f z / ((‖z‖ ^ 2 : ℝ) : ℂ) =
        h z / ((‖z‖ ^ 2 : ℝ) : ℂ) + f 0 * (G z / ((‖z‖ ^ 2 : ℝ) : ℂ)) := by
      intro z; rw [hhdef]; ring
    simp_rw [e]
    rw [integral_add (hsetint hh_int δ hδ) ((hsetint hG_int δ hδ).const_mul _),
      integral_const_mul]
    ring
  have hT1 : Tendsto (fun δ : ℝ => ∫ z in {z : ℂ | δ ≤ ‖z‖}, h z / ((‖z‖ ^ 2 : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 (∫ z, h z / ((‖z‖ ^ 2 : ℝ) : ℂ))) := by
    refine tendsto_setIntegral_of_ae_eventually_mem hS hA ?_
    have hne : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := by simp [ae_iff]
    filter_upwards [hne] with z hz
    exact ((eventually_lt_nhds (norm_pos_iff.mpr hz)).filter_mono nhdsWithin_le_nhds).mono
      (fun δ hδ => le_of_lt hδ)
  have hT2 : Tendsto (fun δ : ℝ => (∫ z in {z : ℂ | δ ≤ ‖z‖}, G z / ((‖z‖ ^ 2 : ℝ) : ℂ)) +
      2 * π * (Real.log δ : ℂ)) (𝓝[>] 0)
      (𝓝 (-(π:ℂ) * ((Real.eulerMascheroniConstant + Real.log π : ℝ) : ℂ))) := by
    have hT := ((Complex.continuous_ofReal.tendsto _).comp tendsto_E1).const_mul (2 * (π:ℂ))
    have hv : 2 * (π:ℂ) * (((-(Real.eulerMascheroniConstant + Real.log π) / 2 : ℝ)) : ℂ) =
        -(π:ℂ) * ((Real.eulerMascheroniConstant + Real.log π : ℝ) : ℂ) := by
      push_cast; ring
    rw [hv] at hT
    refine hT.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [hGdef, setIntegral_gauss_div hδ]
    simp only [Function.comp_apply]
    push_cast
    ring
  have hlim := hT1.add (hT2.const_mul (f 0))
  have hval : (∫ z, h z / ((‖z‖ ^ 2 : ℝ) : ℂ)) +
      f 0 * (-(π:ℂ) * ((Real.eulerMascheroniConstant + Real.log π : ℝ) : ℂ)) =
      -(π : ℂ) * (∫ w : ℂ, (Real.log (‖w‖ ^ 2) : ℂ) * FourierTransform.fourier (f : ℂ → ℂ) w) -
        2 * π * ((Real.eulerMascheroniConstant + Real.log π : ℝ) : ℂ) * f 0 := by
    rw [hId, hlogsplit, hK]
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (hdec δ hδ).symm

end Sol_ExplicitFormula_complex_log_fourier_finite_part

theorem solution (f : SchwartzMap ℂ ℂ) :
    Tendsto
      (fun δ : ℝ => (∫ z in {z : ℂ | δ ≤ ‖z‖}, f z / ((‖z‖ ^ 2 : ℝ) : ℂ)) +
        2 * π * f 0 * (Real.log δ : ℂ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (-(π : ℂ) * (∫ w : ℂ, (Real.log (‖w‖ ^ 2) : ℂ) *
          FourierTransform.fourier (f : ℂ → ℂ) w) -
        2 * π * ((Real.eulerMascheroniConstant + Real.log π : ℝ) : ℂ) * f 0)) :=
  Sol_ExplicitFormula_complex_log_fourier_finite_part.main f
