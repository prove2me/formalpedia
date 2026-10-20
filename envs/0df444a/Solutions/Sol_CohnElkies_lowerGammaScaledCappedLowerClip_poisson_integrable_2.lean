-- Prove2me | solution 2 for CohnElkies.lowerGammaScaledCappedLowerClip_poisson_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:01:20.642954+00:00
-- url     : https://prove2.me/submissions/6e76f12d-166e-487e-aa97-ef5d9139d6c8

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
theorem h47_measurable_cGamma : Measurable Complex.Gamma := by
  have hseq : ∀ n : ℕ, Measurable (fun s : ℂ => Complex.GammaSeq s n) := by
    intro n
    unfold Complex.GammaSeq
    apply Measurable.div
    · exact (measurable_const.pow measurable_id).mul measurable_const
    · exact Finset.measurable_prod _ (fun j _ => measurable_id.add measurable_const)
  exact measurable_of_tendsto_metrizable hseq
    (tendsto_pi_nhds.mpr fun s => Complex.GammaSeq_tendsto_Gamma s)

theorem h47_int_abs_pow_exp (n : ℕ) {a : ℝ} (ha : 0 < a) :
    MeasureTheory.Integrable (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) := by
  have h1 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := a)
    (by have := n.cast_nonneg (α := ℝ); linarith) one_pos ha
  have hIoi : MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) (Set.Ioi 0) := by
    refine h1.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx0 : (0:ℝ) < x := hx
    simp [abs_of_pos hx0, Real.rpow_natCast]
  have hIio : MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) (Set.Iio 0) := by
    have := (show MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) (Set.Ioi (-0)) by
      simpa using hIoi).comp_neg_Iio
    simpa [abs_neg] using this
  have hall : MeasureTheory.IntegrableOn (fun T : ℝ => |T| ^ n * Real.exp (-a * |T|)) (Set.Iic 0 ∪ Set.Ioi 0) :=
    ((integrableOn_Iic_iff_integrableOn_Iio (b := (0:ℝ))).mpr hIio).union hIoi
  rw [Set.Iic_union_Ioi, MeasureTheory.integrableOn_univ] at hall
  exact hall

open CohnElkies in
theorem h47m_Kint {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) :
    Integrable (fun T : ℝ => stripPoissonKernel σ T) := by
  have hpi := Real.pi_pos
  set θ := Real.pi * (1 + σ) / 2 with hθ
  have hθ0 : 0 < θ := by rw [hθ]; nlinarith
  have hθπ : θ < Real.pi := by rw [hθ]; nlinarith
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0.le hθπ.le
  have hc1 : Real.cos θ < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hθπ.le hθ0
    simpa using h
  set m := min 1 (1 - Real.cos θ) with hm
  have hm0 : 0 < m := lt_min one_pos (by linarith)
  have hbound : ∀ T : ℝ, 0 ≤ stripPoissonKernel σ T ∧
      stripPoissonKernel σ T ≤ Real.sin θ / (2 * m) * Real.exp (-(Real.pi / 2) * |T|) := by
    intro T
    unfold stripPoissonKernel stripAngle
    rw [← hθ]
    have hC1 := Real.one_le_cosh (Real.pi * T / 2)
    have hlow : m * Real.cosh (Real.pi * T / 2) ≤ Real.cosh (Real.pi * T / 2) - Real.cos θ := by
      rcases le_total (Real.cos θ) 0 with h | h
      · have : m ≤ 1 := min_le_left _ _
        nlinarith
      · have : m ≤ 1 - Real.cos θ := min_le_right _ _
        nlinarith
    have hch : Real.exp (Real.pi / 2 * |T|) / 2 ≤ Real.cosh (Real.pi * T / 2) := by
      rw [← Real.cosh_abs, Real.cosh_eq]
      have : |Real.pi * T / 2| = Real.pi / 2 * |T| := by
        rw [abs_div, abs_mul, abs_of_pos hpi]; norm_num; ring
      rw [this]
      linarith [Real.exp_pos (-(Real.pi / 2 * |T|))]
    have hG := Real.exp_pos (Real.pi / 2 * |T|)
    have hFG : Real.exp (-(Real.pi / 2) * |T|) * Real.exp (Real.pi / 2 * |T|) = 1 := by
      rw [← Real.exp_add]; ring_nf; simp
    have hD0 : 0 < 4 * (Real.cosh (Real.pi * T / 2) - Real.cos θ) := by nlinarith
    refine ⟨div_nonneg hs hD0.le, ?_⟩
    rw [div_le_iff₀ hD0]
    have hD1 : 2 * m * Real.exp (Real.pi / 2 * |T|) ≤ 4 * (Real.cosh (Real.pi * T / 2) - Real.cos θ) := by
      nlinarith
    have hF := Real.exp_pos (-(Real.pi / 2) * |T|)
    calc Real.sin θ = Real.sin θ / (2 * m) * Real.exp (-(Real.pi / 2) * |T|) *
          (2 * m * Real.exp (Real.pi / 2 * |T|)) := by
          have h2m : (2 * m) ≠ 0 := by positivity
          rw [show Real.sin θ / (2 * m) * Real.exp (-(Real.pi / 2) * |T|) * (2 * m * Real.exp (Real.pi / 2 * |T|))
              = Real.sin θ * (Real.exp (-(Real.pi / 2) * |T|) * Real.exp (Real.pi / 2 * |T|)) * ((2 * m) / (2 * m)) by ring,
            hFG, div_self h2m]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hD1 (by positivity)
  have hmaj : Integrable (fun T : ℝ => Real.sin θ / (2 * m) * Real.exp (-(Real.pi / 2) * |T|)) := by
    refine ((h47_int_abs_pow_exp 0 (by positivity : (0:ℝ) < Real.pi / 2)).const_mul
      (Real.sin θ / (2 * m))).congr (Filter.Eventually.of_forall fun T => ?_)
    simp
  have hK : Integrable (fun T : ℝ => stripPoissonKernel σ T) := by
    have hmeas : Measurable (fun T : ℝ => stripPoissonKernel σ T) := by
      unfold stripPoissonKernel; fun_prop
    refine hmaj.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun T => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hbound T).1]
    exact (hbound T).2
  exact hK

open CohnElkies in
theorem h47m_mass {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) :
    ∫ T : ℝ, stripPoissonKernel σ T = stripBottomMass σ := by
  have hpi := Real.pi_pos
  set θ := stripAngle σ with hθdef
  have hθ0 : 0 < θ := by rw [hθdef]; unfold stripAngle; nlinarith
  have hθπ : θ < Real.pi := by rw [hθdef]; unfold stripAngle; nlinarith
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hderiv : ∀ T : ℝ, HasDerivAt (stripPoissonPrimitive σ) (stripPoissonKernel σ T) T := by
    intro T
    have h1 : HasDerivAt (fun T : ℝ => Real.pi * T / 2) (Real.pi / 2) T := by
      simpa using ((hasDerivAt_id T).const_mul Real.pi).div_const 2
    have h2 := ((h1.exp.sub_const (Real.cos θ)).div_const (Real.sin θ)).arctan.div_const Real.pi
    unfold stripPoissonPrimitive
    rw [← hθdef]
    refine h2.congr_deriv ?_
    unfold stripPoissonKernel
    rw [← hθdef]
    set E := Real.exp (Real.pi * T / 2) with hE
    have hEpos : 0 < E := Real.exp_pos _
    have hcosh : Real.cosh (Real.pi * T / 2) = (E + E⁻¹) / 2 := by
      rw [Real.cosh_eq, Real.exp_neg]
    rw [hcosh]
    have hsc := Real.sin_sq_add_cos_sq θ
    have hD : 0 < E ^ 2 - 2 * E * Real.cos θ + 1 := by
      nlinarith [sq_nonneg (E - Real.cos θ), hs]
    have hD2 : (E + E⁻¹) / 2 - Real.cos θ = (E ^ 2 - 2 * E * Real.cos θ + 1) / (2 * E) := by
      field_simp; ring
    rw [hD2]
    have hD3 : 1 + ((E - Real.cos θ) / Real.sin θ) ^ 2 = (E ^ 2 - 2 * E * Real.cos θ + 1) / Real.sin θ ^ 2 := by
      field_simp; nlinarith [hsc]
    rw [hD3]
    field_simp
    ring
  have hbot : Filter.Tendsto (stripPoissonPrimitive σ) Filter.atBot (nhds ((θ - Real.pi / 2) / Real.pi)) := by
    have hlim : Filter.Tendsto (fun T : ℝ => Real.exp (Real.pi * T / 2)) Filter.atBot (nhds 0) := by
      apply Real.tendsto_exp_atBot.comp
      apply Filter.Tendsto.atBot_div_const two_pos
      exact Filter.Tendsto.const_mul_atBot hpi Filter.tendsto_id
    have hval : Real.arctan ((0 - Real.cos θ) / Real.sin θ) = θ - Real.pi / 2 := by
      have : (0 - Real.cos θ) / Real.sin θ = Real.tan (θ - Real.pi / 2) := by
        rw [Real.tan_eq_sin_div_cos, Real.sin_sub_pi_div_two, Real.cos_sub_pi_div_two]; ring
      rw [this, Real.arctan_tan] <;> linarith
    unfold stripPoissonPrimitive
    rw [← hθdef, ← hval]
    apply Filter.Tendsto.div_const
    apply (Real.continuous_arctan.tendsto _).comp
    exact ((hlim.sub_const _).div_const _)
  have htop : Filter.Tendsto (stripPoissonPrimitive σ) Filter.atTop (nhds ((Real.pi / 2) / Real.pi)) := by
    have hlim : Filter.Tendsto (fun T : ℝ => Real.exp (Real.pi * T / 2)) Filter.atTop Filter.atTop := by
      apply Real.tendsto_exp_atTop.comp
      apply Filter.Tendsto.atTop_div_const two_pos
      exact Filter.Tendsto.const_mul_atTop hpi Filter.tendsto_id
    unfold stripPoissonPrimitive
    rw [← hθdef]
    apply Filter.Tendsto.div_const
    apply tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop |>.comp
    exact Filter.Tendsto.atTop_div_const hs (Filter.tendsto_atTop_add_const_right _ _ hlim)
  rw [integral_of_hasDerivAt_of_tendsto hderiv (h47m_Kint hbelow habove) hbot htop]
  unfold stripBottomMass
  rw [hθdef]; unfold stripAngle
  field_simp
  ring

theorem solution
    {d : ℕ} (hd : 0 < d) {c D n σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    Integrable (fun Y : ℝ =>
      stripPoissonKernel σ (s - Y) *
        lowerGammaScaledCappedLowerClip d c D n Y) := by
  have hLB : Measurable (fun y : ℝ => lowerGammaBoundaryLog ((d : ℝ) / 2) (c * Real.sqrt d) y) := by
    unfold lowerGammaBoundaryLog
    have hg := h47_measurable_cGamma
    have h1 : Measurable (fun y : ℝ => -Complex.I * (y : ℂ) / 2) := by fun_prop
    have h2 : Measurable (fun y : ℝ => (((d : ℝ) / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ) / 2) := by fun_prop
    exact (measurable_const.add (((hg.comp h1).norm).log)).sub ((hg.comp h2).norm.log)
  have hcap : Measurable (fun y : ℝ => lowerGammaBoundaryCapped ((d : ℝ) / 2) (c * Real.sqrt d) D y) := by
    unfold lowerGammaBoundaryCapped
    exact Measurable.ite (measurableSet_singleton 0) measurable_const (hLB.min measurable_const)
  have hcapD : ∀ y, lowerGammaBoundaryCapped ((d : ℝ) / 2) (c * Real.sqrt d) D y ≤ D := by
    intro y; unfold lowerGammaBoundaryCapped; split_ifs
    · exact le_rfl
    · exact min_le_right _ _
  have hLmeas : Measurable (fun Y : ℝ => lowerGammaScaledCappedLowerClip d c D n Y) := by
    unfold lowerGammaScaledCappedLowerClip
    exact (hcap.comp (measurable_const.mul measurable_id)).max measurable_const
  have hLbd : ∀ Y, ‖lowerGammaScaledCappedLowerClip d c D n Y‖ ≤ |n| + |D| := by
    intro Y
    unfold lowerGammaScaledCappedLowerClip
    have := hcapD (((d : ℝ) / 2) * Y)
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := le_max_right (lowerGammaBoundaryCapped ((d : ℝ) / 2) (c * Real.sqrt d) D (((d : ℝ) / 2) * Y)) (-n)
      have := le_abs_self n; have := abs_nonneg D; linarith
    · apply max_le
      · have := le_abs_self D; have := abs_nonneg n; linarith
      · have := neg_le_abs n; have := abs_nonneg D; linarith
  have hK := h47m_Kint hbelow habove
  have hKs : Integrable (fun Y : ℝ => stripPoissonKernel σ (s - Y)) := hK.comp_sub_left s
  have hKnn : ∀ T, 0 ≤ stripPoissonKernel σ T := by
    intro T
    unfold stripPoissonKernel stripAngle
    have hpi := Real.pi_pos
    have hθ0 : 0 < Real.pi * (1 + σ) / 2 := by nlinarith
    have hθπ : Real.pi * (1 + σ) / 2 < Real.pi := by nlinarith
    have hc1 : Real.cos (Real.pi * (1 + σ) / 2) < 1 := by
      have h := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hθπ.le hθ0
      simpa using h
    apply div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ0.le hθπ.le)
    have := Real.one_le_cosh (Real.pi * T / 2)
    linarith
  have hI1 : Integrable (fun Y : ℝ => stripPoissonKernel σ (s - Y) * lowerGammaScaledCappedLowerClip d c D n Y) := by
    refine (hKs.mul_const (|n| + |D|)).mono' ?_ (Filter.Eventually.of_forall fun Y => ?_)
    · exact hKs.1.mul hLmeas.aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hKnn _)]
      exact mul_le_mul_of_nonneg_left (hLbd Y) (hKnn _)
  exact hI1

