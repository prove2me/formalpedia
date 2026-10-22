-- Prove2me | solution 1 for FlexApproval.Statics.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T22:34:40.626877+00:00
-- url     : https://prove2.me/submissions/5c1e63c8-f051-4e1f-8c75-c2a0cffc7074

import Mathlib
import Definitions.Def_FlexApproval_Statics_Model

set_option autoImplicit false

open Cohen2019.Robust FlexApproval.Statics

/-! ### Phi facts (copied from our accepted Cohen2019 siblings) -/

open MeasureTheory ProbabilityTheory in
theorem fa_phi_strictMono : StrictMono Cohen2019.Robust.Phi := by
  intro a b hab
  unfold Cohen2019.Robust.Phi
  have hv : (1 : NNReal) ≠ 0 := one_ne_zero
  have hpos : (gaussianReal 0 1) (Set.Ioc a b) ≠ 0 := by
    intro h
    have h2 := gaussianReal_absolutelyContinuous' (0 : ℝ) hv h
    rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at h2
    linarith
  have hm := (cdf (gaussianReal 0 1)).measure_Ioc a b
  rw [measure_cdf] at hm
  rw [hm] at hpos
  have : ¬ (cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a ≤ 0) := by
    intro hle; exact hpos (ENNReal.ofReal_eq_zero.mpr hle)
  linarith

open MeasureTheory ProbabilityTheory in
theorem fa_phi_continuous : Continuous Cohen2019.Robust.Phi := by
  have hfun : Cohen2019.Robust.Phi = fun t => cdf (gaussianReal 0 1) t := rfl
  rw [hfun, continuous_iff_continuousAt]
  intro a
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  rw [(monotone_cdf (gaussianReal 0 1)).continuousAt_iff_leftLim_eq_rightLim,
    StieltjesFunction.rightLim_eq]
  have hs := (cdf (gaussianReal 0 1)).measure_singleton a
  rw [measure_cdf, measure_singleton, eq_comm, ENNReal.ofReal_eq_zero] at hs
  have hle := (monotone_cdf (gaussianReal 0 1)).leftLim_le (le_refl a)
  linarith

open MeasureTheory ProbabilityTheory Filter in
theorem fa_phi_inv {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Cohen2019.Robust.Phi (Cohen2019.Robust.PhiInvReal q) = q := by
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot (gaussianReal 0 1)).eventually
    (Iio_mem_nhds hq0)).exists
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop (gaussianReal 0 1)).eventually
    (Ioi_mem_nhds hq1)).exists
  have hmem : q ∈ Set.Icc (Cohen2019.Robust.Phi a) (Cohen2019.Robust.Phi b) :=
    ⟨le_of_lt ha, le_of_lt hb⟩
  obtain ⟨t, ht⟩ := intermediate_value_univ a b fa_phi_continuous hmem
  have hS : {s : ℝ | q ≤ Cohen2019.Robust.Phi s} = Set.Ici t := by
    ext s
    simp only [Set.mem_Ici]
    rw [← ht]
    exact fa_phi_strictMono.le_iff_le
  unfold Cohen2019.Robust.PhiInvReal
  rw [hS, csInf_Ici, ht]

open ProbabilityTheory in
theorem fa_phi_nonneg (t : ℝ) : 0 ≤ Phi t := by
  unfold Phi; exact cdf_nonneg _ t

open ProbabilityTheory in
theorem fa_phi_le_one (t : ℝ) : Phi t ≤ 1 := by
  unfold Phi; exact cdf_le_one _ t

theorem fa_phi_pos (t : ℝ) : 0 < Phi t :=
  lt_of_le_of_lt (fa_phi_nonneg (t - 1)) (fa_phi_strictMono (by linarith))

theorem fa_phi_lt_one (t : ℝ) : Phi t < 1 :=
  lt_of_lt_of_le (fa_phi_strictMono (by linarith : t < t + 1)) (fa_phi_le_one _)

/-! ### Derivative of Phi -/

open MeasureTheory ProbabilityTheory in
theorem fa_phi_eq (t : ℝ) :
    Phi t = Phi 0 + ∫ x in (0:ℝ)..t, gaussianPDFReal 0 1 x := by
  have hI : ∀ s : ℝ, Phi s = ∫ x in Set.Iic s, gaussianPDFReal 0 1 x := by
    intro s
    rw [Phi, cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
      ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg _ _ x))]
  rw [hI t, hI 0, ← intervalIntegral.integral_Iic_sub_Iic
    (integrable_gaussianPDFReal 0 1).integrableOn (integrable_gaussianPDFReal 0 1).integrableOn]
  ring

open ProbabilityTheory in
theorem fa_pdf_cont : Continuous (gaussianPDFReal 0 1) := by
  rw [gaussianPDFReal_def]; fun_prop

open ProbabilityTheory in
theorem fa_phi_hasDeriv (t : ℝ) : HasDerivAt Phi (gaussianPDFReal 0 1 t) t := by
  have h := ((fa_pdf_cont.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add (Phi 0)
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => fa_phi_eq s))

open ProbabilityTheory in
theorem fa_pdf_eq (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
  simp [gaussianPDFReal]

/-! ### The inverse PhiInvReal -/

theorem fa_inv_strictMonoOn : StrictMonoOn PhiInvReal (Set.Ioo 0 1) := by
  intro p hp q hq hpq
  rw [← fa_phi_strictMono.lt_iff_lt, fa_phi_inv hp.1 hp.2, fa_phi_inv hq.1 hq.2]
  exact hpq

theorem fa_inv_contAt {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : ContinuousAt PhiInvReal p := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hlo : Phi (PhiInvReal p - ε) < p := by
    have := fa_phi_strictMono (show PhiInvReal p - ε < PhiInvReal p by linarith)
    rwa [fa_phi_inv hp0 hp1] at this
  have hhi : p < Phi (PhiInvReal p + ε) := by
    have := fa_phi_strictMono (show PhiInvReal p < PhiInvReal p + ε by linarith)
    rwa [fa_phi_inv hp0 hp1] at this
  refine ⟨min (p - Phi (PhiInvReal p - ε)) (Phi (PhiInvReal p + ε) - p),
    lt_min (by linarith) (by linarith), ?_⟩
  intro q hq
  rw [Real.dist_eq] at hq ⊢
  have h1 := lt_of_lt_of_le hq (min_le_left _ _)
  have h2 := lt_of_lt_of_le hq (min_le_right _ _)
  rw [abs_lt] at h1 h2
  have hq0 : 0 < q := by linarith [fa_phi_pos (PhiInvReal p - ε)]
  have hq1 : q < 1 := by linarith [fa_phi_lt_one (PhiInvReal p + ε)]
  have hA : PhiInvReal p - ε < PhiInvReal q := by
    rw [← fa_phi_strictMono.lt_iff_lt, fa_phi_inv hq0 hq1]; linarith
  have hB : PhiInvReal q < PhiInvReal p + ε := by
    rw [← fa_phi_strictMono.lt_iff_lt, fa_phi_inv hq0 hq1]; linarith
  rw [abs_lt]; constructor <;> linarith

open ProbabilityTheory in
theorem fa_inv_hasDeriv {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt PhiInvReal (gaussianPDFReal 0 1 (PhiInvReal p))⁻¹ p := by
  apply HasDerivAt.of_local_left_inverse (fa_inv_contAt hp0 hp1) (fa_phi_hasDeriv _)
    (gaussianPDFReal_pos _ _ _ one_ne_zero).ne'
  filter_upwards [isOpen_Ioo.mem_nhds ⟨hp0, hp1⟩] with y hy
  exact fa_phi_inv hy.1 hy.2

/-! ### The power curve pw -/

theorem fa_pw_mid {θ α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    pw θ α = 1 - Phi (PhiInvReal (1 - α) - θ) := by
  simp [pw, not_le.mpr h0, not_le.mpr h1]

theorem fa_pw_zero (θ : ℝ) : pw θ 0 = 0 := by simp [pw]

theorem fa_pw_one (θ : ℝ) : pw θ 1 = 1 := by simp [pw]

theorem fa_pw_mem (θ α : ℝ) : 0 ≤ pw θ α ∧ pw θ α ≤ 1 := by
  unfold pw
  split_ifs
  · norm_num
  · norm_num
  · constructor <;> linarith [fa_phi_nonneg (PhiInvReal (1 - α) - θ),
      fa_phi_le_one (PhiInvReal (1 - α) - θ)]

theorem fa_pw_ge {θ α : ℝ} (hθ : 0 ≤ θ) (hα : α ∈ Set.Icc (0:ℝ) 1) : α ≤ pw θ α := by
  rcases eq_or_lt_of_le hα.1 with h | h
  · rw [← h, fa_pw_zero]
  rcases eq_or_lt_of_le hα.2 with h' | h'
  · rw [h', fa_pw_one]
  rw [fa_pw_mid h h']
  have := fa_phi_strictMono.monotone (show PhiInvReal (1 - α) - θ ≤ PhiInvReal (1 - α) by linarith)
  rw [fa_phi_inv (by linarith) (by linarith)] at this
  linarith

theorem fa_pw_mono {θ : ℝ} : MonotoneOn (pw θ) (Set.Icc 0 1) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hx.1 with h | h
  · rw [← h, fa_pw_zero]; exact (fa_pw_mem θ y).1
  rcases eq_or_lt_of_le hy.2 with h' | h'
  · rw [h', fa_pw_one]; exact (fa_pw_mem θ x).2
  rw [fa_pw_mid h (lt_of_le_of_lt hxy h'), fa_pw_mid (lt_of_lt_of_le h hxy) h']
  have h3 := fa_inv_strictMonoOn.monotoneOn (show 1 - y ∈ Set.Ioo (0:ℝ) 1 by
    constructor <;> linarith) (show 1 - x ∈ Set.Ioo (0:ℝ) 1 by
    constructor <;> linarith [lt_of_le_of_lt hxy h']) (by linarith : 1 - y ≤ 1 - x)
  have h4 := fa_phi_strictMono.monotone
    (by linarith : PhiInvReal (1 - y) - θ ≤ PhiInvReal (1 - x) - θ)
  linarith

theorem fa_pw_hasDeriv {θ α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    HasDerivAt (pw θ) (gp θ α) α := by
  have hin := fa_inv_hasDeriv (show 0 < 1 - α by linarith) (show 1 - α < 1 by linarith)
  have hlin : HasDerivAt (fun y : ℝ => 1 - y) (-1) α := by
    simpa using (hasDerivAt_id α).const_sub 1
  have hcomp := ((fa_phi_hasDeriv (PhiInvReal (1 - α) - θ)).comp α
      ((hin.comp α hlin).sub_const θ)).const_sub 1
  have heq : pw θ =ᶠ[nhds α] (fun y => 1 - Phi (PhiInvReal (1 - y) - θ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨h0, h1⟩] with y hy
    exact fa_pw_mid hy.1 hy.2
  refine (hcomp.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [gp, fa_pdf_eq, fa_pdf_eq]
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have key : Real.exp (-(PhiInvReal (1 - α) - θ) ^ 2 / 2) =
      Real.exp (θ * PhiInvReal (1 - α) - θ ^ 2 / 2) * Real.exp (-(PhiInvReal (1 - α)) ^ 2 / 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [key]
  field_simp

theorem fa_gp_anti {θ : ℝ} (hθ : 0 < θ) : StrictAntiOn (gp θ) (Set.Ioo 0 1) := by
  intro x hx y hy hxy
  unfold gp
  apply Real.exp_lt_exp.mpr
  have : PhiInvReal (1 - y) < PhiInvReal (1 - x) :=
    fa_inv_strictMonoOn ⟨by linarith [hy.2], by linarith [hy.1]⟩
      ⟨by linarith [hx.2], by linarith [hx.1]⟩ (by linarith)
  nlinarith

open Filter ProbabilityTheory in
theorem fa_pw_cont {θ : ℝ} (hθ : 0 ≤ θ) : ContinuousOn (pw θ) (Set.Icc 0 1) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with h0 | h0
  · rw [← h0, Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp ((tendsto_cdf_atTop
      (gaussianReal 0 1)).eventually (Ioi_mem_nhds (show 1 - ε < 1 by linarith)))
    refine ⟨1 - Phi (M + θ), by linarith [fa_phi_lt_one (M + θ)], ?_⟩
    intro y hy hdy
    rw [Real.dist_eq, sub_zero] at hdy
    rw [Real.dist_eq, fa_pw_zero, sub_zero]
    rcases eq_or_lt_of_le hy.1 with hy0 | hy0
    · rw [← hy0, fa_pw_zero]; simpa using hε
    have hy1 : y < 1 := by
      have := abs_lt.mp hdy; linarith [fa_phi_pos (M + θ)]
    rw [fa_pw_mid hy0 hy1, abs_lt]
    have hT : M + θ < PhiInvReal (1 - y) := by
      by_contra hc
      push_neg at hc
      have := fa_phi_strictMono.monotone hc
      rw [fa_phi_inv (by linarith) (by linarith)] at this
      have := abs_lt.mp hdy
      linarith
    have hP : 1 - ε < Phi (PhiInvReal (1 - y) - θ) := hM _ (by linarith)
    constructor <;> linarith [fa_phi_le_one (PhiInvReal (1 - y) - θ)]
  rcases eq_or_lt_of_le hx.2 with h1 | h1
  · rw [h1, Metric.continuousWithinAt_iff]
    intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro y hy hdy
    rw [Real.dist_eq] at hdy ⊢
    rw [fa_pw_one]
    have := fa_pw_ge hθ hy
    have := (fa_pw_mem θ y).2
    rw [abs_lt] at hdy ⊢
    constructor <;> linarith
  exact (fa_pw_hasDeriv h0 h1).continuousAt.continuousWithinAt

theorem fa_pw_sconc {θ : ℝ} (hθ : 0 < θ) : StrictConcaveOn ℝ (Set.Icc 0 1) (pw θ) := by
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Icc 0 1) (fa_pw_cont hθ.le)
  rw [interior_Icc]
  intro x hx y hy hxy
  rw [(fa_pw_hasDeriv hx.1 hx.2).deriv, (fa_pw_hasDeriv hy.1 hy.2).deriv]
  exact fa_gp_anti hθ hx hy hxy

/-! ### The model: V as a function of the power curve -/

noncomputable def fa_h (s : ℝ) : ℝ := s / (1 + s)

noncomputable def fa_c (P : Params) : ℝ := lamTilde P * P.p / ((P.K : ℝ) * P.muE)

theorem fa_psiE_eq (P : Params) (α : ℝ) : psiE P α = fa_c P * pw (theta P) α := by
  simp only [psiE, lamAE, piAE, fa_c]; ring

theorem fa_V_eq (P : Params) (α : ℝ) : V P α =
    P.WTP * P.QE * P.K * fa_h (psiE P α)
    + lamTilde P * (P.CAE + P.CRE) * P.p * pw (theta P) α
    - lamTilde P * (1 - P.p) * (P.WTP * P.QI / P.muI + P.CAI) * α
    - lamTilde P * P.CRE * P.p := by
  simp only [V, ENE, ENI, fa_h, psiI, lamAE, lamAI, lamRE, piAE, piAI, piRE]
  ring

theorem fa_Vd (P : Params) (α β : ℝ) : V P α - V P β =
    P.WTP * P.QE * P.K * (fa_h (fa_c P * pw (theta P) α) - fa_h (fa_c P * pw (theta P) β))
    + lamTilde P * (P.CAE + P.CRE) * P.p * (pw (theta P) α - pw (theta P) β)
    - lamTilde P * (1 - P.p) * (P.WTP * P.QI / P.muI + P.CAI) * (α - β) := by
  rw [fa_V_eq, fa_V_eq, fa_psiE_eq, fa_psiE_eq]; ring

theorem fa_K_pos {P : Params} (h : P.Standing) : (0:ℝ) < P.K := by
  have hK := h.2.2.2.2.2.2.2.2.2.2.1
  exact_mod_cast (show 0 < P.K by omega)

theorem fa_L_pos {P : Params} (h : P.Standing) : 0 < lamTilde P := by
  obtain ⟨_, _, _, _, _, hl, hct, hab, _⟩ := h
  unfold lamTilde
  exact div_pos (mul_pos hl hct) (add_pos hct hab)

theorem fa_c_pos {P : Params} (h : P.Standing) : 0 < fa_c P := by
  have hL := fa_L_pos h
  have hK := fa_K_pos h
  obtain ⟨hp, _, _, _, _, _, _, _, hE, _⟩ := h
  unfold fa_c
  exact div_pos (mul_pos hL hp) (mul_pos hK hE)

theorem fa_theta_pos {P : Params} (h : P.Standing) : 0 < theta P := by
  obtain ⟨_, _, hd, hs, hn, _⟩ := h
  unfold theta In
  have hn' : (0:ℝ) < P.n := by exact_mod_cast (show 0 < P.n by omega)
  exact mul_pos hd (Real.sqrt_pos.mpr (div_pos hn' (by positivity)))

theorem fa_A_pos {P : Params} (h : P.Standing) : 0 < P.WTP * P.QE * P.K := by
  have hK := fa_K_pos h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hW, hQ, _⟩ := h
  positivity

/-! ### Algebra of h(s) = s / (1 + s) -/

theorem fa_h_lt {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) : fa_h s < fa_h t := by
  unfold fa_h; rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith

theorem fa_h_le {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : fa_h s ≤ fa_h t := by
  unfold fa_h; rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith

theorem fa_h_conc {x y a b : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : a * fa_h x + b * fa_h y ≤ fa_h (a * x + b * y) := by
  obtain rfl : b = 1 - a := by linarith
  unfold fa_h
  have hX : 0 < 1 + x := by linarith
  have hY : 0 < 1 + y := by linarith
  have hZ : 0 < 1 + (a * x + (1 - a) * y) := by nlinarith
  rw [show a * (x / (1 + x)) + (1 - a) * (y / (1 + y)) =
      (a * x * (1 + y) + (1 - a) * y * (1 + x)) / ((1 + x) * (1 + y)) by field_simp]
  rw [div_le_div_iff₀ (by positivity) hZ]
  nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x - y))]

theorem fa_h_sub {c u v : ℝ} (hc : 0 ≤ c) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    fa_h (c * u) - fa_h (c * v) = c * (u - v) / ((1 + c * u) * (1 + c * v)) := by
  unfold fa_h
  have h1 : 0 < 1 + c * u := by nlinarith
  have h2 : 0 < 1 + c * v := by nlinarith
  field_simp; ring

/-- the increment of `h` in the scale `c` grows with `c` while `c u ≤ 1` -/
theorem fa_h_dm {c₁ c₂ u v : ℝ} (hc1 : 0 ≤ c₁) (hc12 : c₁ ≤ c₂) (hv : 0 ≤ v) (hvu : v ≤ u)
    (h1 : c₂ * u ≤ 1) :
    fa_h (c₁ * u) - fa_h (c₁ * v) ≤ fa_h (c₂ * u) - fa_h (c₂ * v) := by
  have hu : 0 ≤ u := le_trans hv hvu
  have hc2 : 0 ≤ c₂ := le_trans hc1 hc12
  rw [fa_h_sub hc1 hu hv, fa_h_sub hc2 hu hv]
  have e1 : 0 < (1 + c₁ * u) * (1 + c₁ * v) := by positivity
  have e2 : 0 < (1 + c₂ * u) * (1 + c₂ * v) := by positivity
  rw [div_le_div_iff₀ e1 e2]
  have hcv : c₂ * v ≤ c₂ * u := mul_le_mul_of_nonneg_left hvu hc2
  have hcv0 : 0 ≤ c₂ * v := mul_nonneg hc2 hv
  have hk : c₁ * c₂ * u * v ≤ 1 := by
    have : c₁ * (c₂ * u * v) ≤ c₂ * (c₂ * u * v) :=
      mul_le_mul_of_nonneg_right hc12 (by positivity)
    nlinarith
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hvu) (sub_nonneg.2 hc12)) (sub_nonneg.2 hk)]

/-- the increment of `h(L k u)`, divided by `L`, falls as `L` grows -/
theorem fa_h_L {L₁ L₂ q m u v : ℝ} (hL1 : 0 < L₁) (hL12 : L₁ ≤ L₂) (hq : 0 ≤ q) (hm : 0 < m)
    (hv : 0 ≤ v) (hvu : v ≤ u) :
    L₁ * (fa_h (L₂ * q / m * u) - fa_h (L₂ * q / m * v)) ≤
      L₂ * (fa_h (L₁ * q / m * u) - fa_h (L₁ * q / m * v)) := by
  have hu : 0 ≤ u := le_trans hv hvu
  have hk1 : 0 ≤ L₁ * q / m := by positivity
  have hk2 : L₁ * q / m ≤ L₂ * q / m := by
    apply div_le_div_of_nonneg_right _ hm.le
    exact mul_le_mul_of_nonneg_right hL12 hq
  have hk2' : 0 ≤ L₂ * q / m := le_trans hk1 hk2
  rw [fa_h_sub hk1 hu hv, fa_h_sub hk2' hu hv]
  have e1 : 0 < (1 + L₁ * q / m * u) * (1 + L₁ * q / m * v) := by positivity
  have e2 : 0 < (1 + L₂ * q / m * u) * (1 + L₂ * q / m * v) := by positivity
  rw [← mul_div_assoc, ← mul_div_assoc, div_le_div_iff₀ e2 e1]
  have hD : (1 + L₁ * q / m * u) * (1 + L₁ * q / m * v) ≤
      (1 + L₂ * q / m * u) * (1 + L₂ * q / m * v) := by
    apply mul_le_mul _ _ (by positivity) (by positivity)
    · nlinarith [mul_le_mul_of_nonneg_right hk2 hu]
    · nlinarith [mul_le_mul_of_nonneg_right hk2 hv]
  have hs : L₁ * (L₂ * q / m * (u - v)) = L₂ * (L₁ * q / m * (u - v)) := by ring
  rw [hs]
  have : 0 ≤ L₁ * q / m * (u - v) := mul_nonneg hk1 (sub_nonneg.2 hvu)
  exact mul_le_mul_of_nonneg_left hD (mul_nonneg (by linarith) this)

/-! ### Strict concavity of V and its consequences -/

theorem fa_V_sconc {P : Params} (hP : P.Standing) : StrictConcaveOn ℝ (Set.Icc 0 1) (V P) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hpw := (fa_pw_sconc (fa_theta_pos hP)).2 hx hy hxy ha hb hab
  simp only [smul_eq_mul] at hpw ⊢
  rw [fa_V_eq, fa_V_eq, fa_V_eq, fa_psiE_eq, fa_psiE_eq, fa_psiE_eq]
  have hc := fa_c_pos hP
  have hA := fa_A_pos hP
  have hux := fa_pw_mem (theta P) x
  have huy := fa_pw_mem (theta P) y
  have hm0 : 0 ≤ a * pw (theta P) x + b * pw (theta P) y := by
    have := mul_nonneg ha.le hux.1; have := mul_nonneg hb.le huy.1; linarith
  have h1 : fa_h (fa_c P * (a * pw (theta P) x + b * pw (theta P) y)) <
      fa_h (fa_c P * pw (theta P) (a * x + b * y)) :=
    fa_h_lt (mul_nonneg hc.le hm0) (mul_lt_mul_of_pos_left hpw hc)
  have h2 := fa_h_conc (x := fa_c P * pw (theta P) x) (y := fa_c P * pw (theta P) y)
    (mul_nonneg hc.le hux.1) (mul_nonneg hc.le huy.1) ha.le hb.le hab
  rw [show a * (fa_c P * pw (theta P) x) + b * (fa_c P * pw (theta P) y) =
    fa_c P * (a * pw (theta P) x + b * pw (theta P) y) by ring] at h2
  have hE : 0 ≤ lamTilde P * (P.CAE + P.CRE) * P.p := by
    have hL := fa_L_pos hP
    obtain ⟨hp, _, _, _, _, _, _, _, _, _, _, _, _, _, hCAE, _, hCRE, _⟩ := hP
    have : 0 ≤ P.CAE + P.CRE := by linarith
    positivity
  have h3 := mul_lt_mul_of_pos_left (lt_of_le_of_lt h2 h1) hA
  have h4 := mul_le_mul_of_nonneg_left hpw.le hE
  have h5 : a * (lamTilde P * P.CRE * P.p) + b * (lamTilde P * P.CRE * P.p) =
      lamTilde P * P.CRE * P.p := by rw [← add_mul, hab, one_mul]
  have h6 : a * (lamTilde P * (1 - P.p) * (P.WTP * P.QI / P.muI + P.CAI) * x) +
      b * (lamTilde P * (1 - P.p) * (P.WTP * P.QI / P.muI + P.CAI) * y) =
      lamTilde P * (1 - P.p) * (P.WTP * P.QI / P.muI + P.CAI) * (a * x + b * y) := by ring
  nlinarith

theorem fa_unique {P : Params} (hP : P.Standing) {a b : ℝ} (ha : IsOptimal P a)
    (hb : b ∈ Set.Icc (0:ℝ) 1) (hle : V P a ≤ V P b) : b = a := by
  by_contra hne
  have hs := (fa_V_sconc hP).2 ha.1 hb (Ne.symm hne) (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (0:ℝ) < 1/2) (by norm_num)
  have hm : (1/2 : ℝ) • a + (1/2 : ℝ) • b ∈ Set.Icc (0:ℝ) 1 :=
    (convex_Icc 0 1) ha.1 hb (by norm_num) (by norm_num) (by norm_num)
  have := ha.2 _ hm
  simp only [smul_eq_mul] at hs this
  linarith

theorem fa_local {P : Params} (hP : P.Standing) {a b α : ℝ} (ha : IsOptimal P a)
    (hb : b ∈ Set.Icc (0:ℝ) 1) (hbα : b < α) (hαa : α ≤ a) (hle : V P α ≤ V P b) : False := by
  have hab : b < a := lt_of_lt_of_le hbα hαa
  have hne : a - b ≠ 0 := (sub_pos.2 hab).ne'
  have ht0 : 0 ≤ (a - α) / (a - b) := div_nonneg (by linarith) (by linarith)
  have ht1 : (a - α) / (a - b) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hα : (a - α) / (a - b) * b + (1 - (a - α) / (a - b)) * a = α := by
    field_simp; ring
  have hc := (fa_V_sconc hP).concaveOn.2 hb ha.1 ht0 (by linarith : (0:ℝ) ≤ 1 - (a - α) / (a - b))
    (by ring)
  simp only [smul_eq_mul] at hc
  rw [hα] at hc
  have h1 : V P a ≤ V P b := by nlinarith
  exact absurd (fa_unique hP ha hb h1) (ne_of_lt hab)

theorem fa_cs_inc {P₁ P₂ : Params} (h1 : P₁.Standing) {a₁ a₂ s₁ s₂ : ℝ}
    (ho1 : IsOptimal P₁ a₁) (ho2 : IsOptimal P₂ a₂) (hs1 : 0 < s₁) (hs2 : 0 < s₂)
    (hd : ∀ β α : ℝ, 0 ≤ β → β < α → α ≤ 1 →
      s₁ * (V P₁ α - V P₁ β) ≤ s₂ * (V P₂ α - V P₂ β)) : a₁ ≤ a₂ := by
  by_contra h
  push_neg at h
  have hd' := hd a₂ a₁ ho2.1.1 h ho1.1.2
  have h2 := ho2.2 a₁ ho1.1
  have : V P₁ a₁ ≤ V P₁ a₂ := by nlinarith
  exact absurd (fa_unique h1 ho1 ho2.1 this) (ne_of_lt h)

theorem fa_near {P : Params} (hP : P.Standing) {b a : ℝ} (hb : b ∈ Set.Icc (0:ℝ) 1)
    (hba : b < a) (ha1 : a ≤ 1) (hψ : psiE P b < 1) :
    ∃ α, b < α ∧ α ≤ a ∧ fa_c P * pw (theta P) α ≤ 1 := by
  rw [fa_psiE_eq] at hψ
  have hcont := (fa_pw_cont (fa_theta_pos hP).le) b hb
  rw [Metric.continuousWithinAt_iff] at hcont
  have hc := fa_c_pos hP
  obtain ⟨δ, hδ, hδ'⟩ := hcont ((1 - fa_c P * pw (theta P) b) / fa_c P)
    (div_pos (by linarith) hc)
  have hlt : b < min a (b + δ / 2) := lt_min hba (by linarith)
  have hle : min a (b + δ / 2) ≤ b + δ / 2 := min_le_right _ _
  refine ⟨min a (b + δ / 2), hlt, min_le_left _ _, ?_⟩
  have hmem : min a (b + δ / 2) ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by linarith [hb.1], le_trans (min_le_left _ _) ha1⟩
  have hd := hδ' hmem (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  rw [Real.dist_eq, abs_lt] at hd
  have h2 := hd.2
  rw [lt_div_iff₀ hc] at h2
  nlinarith

theorem fa_fac {P : Params} (h : P.Standing) {β α : ℝ} (hβ : 0 ≤ β) (hβα : β < α)
    (hα : α ≤ 1) :
    0 ≤ pw (theta P) β ∧ pw (theta P) β ≤ pw (theta P) α ∧ pw (theta P) α ≤ 1 ∧
    fa_h (fa_c P * pw (theta P) β) ≤ fa_h (fa_c P * pw (theta P) α) ∧ 0 < fa_c P ∧
    0 < lamTilde P := by
  have hm := fa_pw_mono (θ := theta P) ⟨hβ, by linarith⟩ ⟨by linarith, hα⟩ hβα.le
  have hr := fa_pw_mem (theta P) β
  have hr' := fa_pw_mem (theta P) α
  have hc := fa_c_pos h
  exact ⟨hr.1, hm, hr'.2, fa_h_le (mul_nonneg hc.le hr.1) (mul_le_mul_of_nonneg_left hm hc.le),
    hc, fa_L_pos h⟩

/-! ### The eleven clauses -/

theorem fa_cl_0 :
    ∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with QE := x₁ } : Params).Standing → ({ P with QE := x₂ } : Params).Standing →
      x₁ ≤ x₂ → IsOptimal { P with QE := x₁ } a₁ → IsOptimal { P with QE := x₂ } a₂ → a₁ ≤ a₂ := by
  intro P x₁ x₂ a₁ a₂ h1 h2 hx ho1 ho2
  refine fa_cs_inc h1 ho1 ho2 one_pos one_pos ?_
  intro β α hβ hβα hα
  obtain ⟨hr, hm, hr', hDh, hc, hL⟩ := fa_fac h1 hβ hβα hα
  have hK := fa_K_pos h1
  obtain ⟨hp0, hp1, -, -, -, hl, hct, hab, hE, hI, -, hW, hQE, hQI, hCAE, hCAI, hCRE, -⟩ := h1
  have eθ : ∀ x, theta { P with QE := x } = theta P := fun _ => rfl
  have ec : ∀ x, fa_c { P with QE := x } = fa_c P := fun _ => rfl
  have eL : ∀ x, lamTilde { P with QE := x } = lamTilde P := fun _ => rfl
  rw [fa_Vd, fa_Vd]
  simp only [eθ, ec, eL] at hr hm hr' hDh hc hL hK hW ⊢
  linarith [mul_nonneg (mul_nonneg (mul_nonneg hW.le (sub_nonneg.2 hx)) hK.le)
    (sub_nonneg.2 hDh)]

theorem fa_cl_1 :
    ∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with CAE := x₁ } : Params).Standing → ({ P with CAE := x₂ } : Params).Standing →
      x₁ ≤ x₂ → IsOptimal { P with CAE := x₁ } a₁ → IsOptimal { P with CAE := x₂ } a₂ → a₁ ≤ a₂ := by
  intro P x₁ x₂ a₁ a₂ h1 h2 hx ho1 ho2
  refine fa_cs_inc h1 ho1 ho2 one_pos one_pos ?_
  intro β α hβ hβα hα
  obtain ⟨hr, hm, hr', hDh, hc, hL⟩ := fa_fac h1 hβ hβα hα
  obtain ⟨hp0, hp1, -, -, -, hl, hct, hab, hE, hI, -, hW, hQE, hQI, hCAE, hCAI, hCRE, -⟩ := h1
  have eθ : ∀ x, theta { P with CAE := x } = theta P := fun _ => rfl
  have ec : ∀ x, fa_c { P with CAE := x } = fa_c P := fun _ => rfl
  have eL : ∀ x, lamTilde { P with CAE := x } = lamTilde P := fun _ => rfl
  rw [fa_Vd, fa_Vd]
  simp only [eθ, ec, eL] at hr hm hr' hDh hc hL hp0 ⊢
  linarith [mul_nonneg (sub_nonneg.2 hx) (mul_nonneg (mul_nonneg hL.le hp0.le)
    (sub_nonneg.2 hm))]

theorem fa_cl_2 :
    ∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with CRE := x₁ } : Params).Standing → ({ P with CRE := x₂ } : Params).Standing →
      x₁ ≤ x₂ → IsOptimal { P with CRE := x₁ } a₁ → IsOptimal { P with CRE := x₂ } a₂ → a₁ ≤ a₂ := by
  intro P x₁ x₂ a₁ a₂ h1 h2 hx ho1 ho2
  refine fa_cs_inc h1 ho1 ho2 one_pos one_pos ?_
  intro β α hβ hβα hα
  obtain ⟨hr, hm, hr', hDh, hc, hL⟩ := fa_fac h1 hβ hβα hα
  obtain ⟨hp0, hp1, -, -, -, hl, hct, hab, hE, hI, -, hW, hQE, hQI, hCAE, hCAI, hCRE, -⟩ := h1
  have eθ : ∀ x, theta { P with CRE := x } = theta P := fun _ => rfl
  have ec : ∀ x, fa_c { P with CRE := x } = fa_c P := fun _ => rfl
  have eL : ∀ x, lamTilde { P with CRE := x } = lamTilde P := fun _ => rfl
  rw [fa_Vd, fa_Vd]
  simp only [eθ, ec, eL] at hr hm hr' hDh hc hL hp0 ⊢
  linarith [mul_nonneg (sub_nonneg.2 hx) (mul_nonneg (mul_nonneg hL.le hp0.le)
    (sub_nonneg.2 hm))]

theorem fa_cl_3 :
    ∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with muI := x₁ } : Params).Standing → ({ P with muI := x₂ } : Params).Standing →
      x₁ ≤ x₂ → IsOptimal { P with muI := x₁ } a₁ → IsOptimal { P with muI := x₂ } a₂ → a₁ ≤ a₂ := by
  intro P x₁ x₂ a₁ a₂ h1 h2 hx ho1 ho2
  refine fa_cs_inc h1 ho1 ho2 one_pos one_pos ?_
  intro β α hβ hβα hα
  obtain ⟨hr, hm, hr', hDh, hc, hL⟩ := fa_fac h1 hβ hβα hα
  obtain ⟨hp0, hp1, -, -, -, hl, hct, hab, hE, hI, -, hW, hQE, hQI, hCAE, hCAI, hCRE, -⟩ := h1
  have eθ : ∀ x, theta { P with muI := x } = theta P := fun _ => rfl
  have ec : ∀ x, fa_c { P with muI := x } = fa_c P := fun _ => rfl
  have eL : ∀ x, lamTilde { P with muI := x } = lamTilde P := fun _ => rfl
  rw [fa_Vd, fa_Vd]
  simp only [eθ, ec, eL] at hr hm hr' hDh hc hL hp1 hI hW hQI ⊢
  have hdiv : P.WTP * P.QI / x₂ ≤ P.WTP * P.QI / x₁ :=
    div_le_div_of_nonneg_left (mul_nonneg hW.le hQI) hI hx
  linarith [mul_nonneg (mul_nonneg (mul_nonneg hL.le (sub_nonneg.2 hp1.le))
    (sub_nonneg.2 hβα.le)) (sub_nonneg.2 hdiv)]

theorem fa_cl_4 :
    ∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with muAB := x₁ } : Params).Standing → ({ P with muAB := x₂ } : Params).Standing →
      x₁ ≤ x₂ → IsOptimal { P with muAB := x₁ } a₁ → IsOptimal { P with muAB := x₂ } a₂ → a₁ ≤ a₂ := by
  intro P x₁ x₂ a₁ a₂ h1 h2 hx ho1 ho2
  have hL1 := fa_L_pos h1
  have hL2 := fa_L_pos h2
  refine fa_cs_inc h1 ho1 ho2 hL2 hL1 ?_
  intro β α hβ hβα hα
  obtain ⟨hr, hm, -, -, -, -⟩ := fa_fac h1 hβ hβα hα
  have hA := fa_A_pos h1
  have hK := fa_K_pos h1
  obtain ⟨hp0, hp1, -, -, -, hl, hct, hab, hE, hI, -, hW, hQE, hQI, hCAE, hCAI, hCRE, -⟩ := h1
  have eθ : ∀ x, theta { P with muAB := x } = theta P := fun _ => rfl
  simp only [eθ] at hr hm hA hK hp0 hl hct hab hE ⊢
  have hL12 : lamTilde { P with muAB := x₂ } ≤ lamTilde { P with muAB := x₁ } := by
    simp only [lamTilde]
    exact div_le_div_of_nonneg_left (mul_nonneg hl.le hct.le) (by linarith) (by linarith)
  have key := fa_h_L hL2 hL12 hp0.le (mul_pos hK hE) hr hm
  rw [fa_Vd, fa_Vd]
  simp only [eθ, fa_c]
  linarith [mul_le_mul_of_nonneg_left key hA.le]

theorem fa_cl_5 :
    ∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with QI := x₁ } : Params).Standing → ({ P with QI := x₂ } : Params).Standing →
      x₁ ≤ x₂ → IsOptimal { P with QI := x₁ } a₁ → IsOptimal { P with QI := x₂ } a₂ → a₂ ≤ a₁ := by
  intro P x₁ x₂ a₁ a₂ h1 h2 hx ho1 ho2
  refine fa_cs_inc h2 ho2 ho1 one_pos one_pos ?_
  intro β α hβ hβα hα
  obtain ⟨hr, hm, hr', hDh, hc, hL⟩ := fa_fac h1 hβ hβα hα
  obtain ⟨hp0, hp1, -, -, -, hl, hct, hab, hE, hI, -, hW, hQE, hQI, hCAE, hCAI, hCRE, -⟩ := h1
  have eθ : ∀ x, theta { P with QI := x } = theta P := fun _ => rfl
  have ec : ∀ x, fa_c { P with QI := x } = fa_c P := fun _ => rfl
  have eL : ∀ x, lamTilde { P with QI := x } = lamTilde P := fun _ => rfl
  rw [fa_Vd, fa_Vd]
  simp only [eθ, ec, eL] at hr hm hr' hDh hc hL hp1 hI hW ⊢
  have hdiv : P.WTP * x₁ / P.muI ≤ P.WTP * x₂ / P.muI :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hx hW.le) hI.le
  linarith [mul_nonneg (mul_nonneg (mul_nonneg hL.le (sub_nonneg.2 hp1.le))
    (sub_nonneg.2 hβα.le)) (sub_nonneg.2 hdiv)]

theorem fa_cl_6 :
    ∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with CAI := x₁ } : Params).Standing → ({ P with CAI := x₂ } : Params).Standing →
      x₁ ≤ x₂ → IsOptimal { P with CAI := x₁ } a₁ → IsOptimal { P with CAI := x₂ } a₂ → a₂ ≤ a₁ := by
  intro P x₁ x₂ a₁ a₂ h1 h2 hx ho1 ho2
  refine fa_cs_inc h2 ho2 ho1 one_pos one_pos ?_
  intro β α hβ hβα hα
  obtain ⟨hr, hm, hr', hDh, hc, hL⟩ := fa_fac h1 hβ hβα hα
  obtain ⟨hp0, hp1, -, -, -, hl, hct, hab, hE, hI, -, hW, hQE, hQI, hCAE, hCAI, hCRE, -⟩ := h1
  have eθ : ∀ x, theta { P with CAI := x } = theta P := fun _ => rfl
  have ec : ∀ x, fa_c { P with CAI := x } = fa_c P := fun _ => rfl
  have eL : ∀ x, lamTilde { P with CAI := x } = lamTilde P := fun _ => rfl
  rw [fa_Vd, fa_Vd]
  simp only [eθ, ec, eL] at hr hm hr' hDh hc hL hp1 ⊢
  linarith [mul_nonneg (mul_nonneg (mul_nonneg hL.le (sub_nonneg.2 hp1.le))
    (sub_nonneg.2 hβα.le)) (sub_nonneg.2 hx)]

theorem fa_cl_7 :
    ∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with lam := x₁ } : Params).Standing → ({ P with lam := x₂ } : Params).Standing →
      x₁ ≤ x₂ → IsOptimal { P with lam := x₁ } a₁ → IsOptimal { P with lam := x₂ } a₂ → a₂ ≤ a₁ := by
  intro P x₁ x₂ a₁ a₂ h1 h2 hx ho1 ho2
  have hL1 := fa_L_pos h1
  have hL2 := fa_L_pos h2
  refine fa_cs_inc h2 ho2 ho1 hL1 hL2 ?_
  intro β α hβ hβα hα
  obtain ⟨hr, hm, -, -, -, -⟩ := fa_fac h1 hβ hβα hα
  have hA := fa_A_pos h1
  have hK := fa_K_pos h1
  obtain ⟨hp0, hp1, -, -, -, hl, hct, hab, hE, hI, -, hW, hQE, hQI, hCAE, hCAI, hCRE, -⟩ := h1
  have eθ : ∀ x, theta { P with lam := x } = theta P := fun _ => rfl
  simp only [eθ] at hr hm hA hK hp0 hl hct hab hE ⊢
  have hL12 : lamTilde { P with lam := x₁ } ≤ lamTilde { P with lam := x₂ } := by
    simp only [lamTilde]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hx hct.le) (by linarith)
  have key := fa_h_L hL1 hL12 hp0.le (mul_pos hK hE) hr hm
  rw [fa_Vd, fa_Vd]
  simp only [eθ, fa_c]
  linarith [mul_le_mul_of_nonneg_left key hA.le]

theorem fa_cl_8 :
    ∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with muCT := x₁ } : Params).Standing → ({ P with muCT := x₂ } : Params).Standing →
      x₁ ≤ x₂ → IsOptimal { P with muCT := x₁ } a₁ → IsOptimal { P with muCT := x₂ } a₂ → a₂ ≤ a₁ := by
  intro P x₁ x₂ a₁ a₂ h1 h2 hx ho1 ho2
  have hL1 := fa_L_pos h1
  have hL2 := fa_L_pos h2
  refine fa_cs_inc h2 ho2 ho1 hL1 hL2 ?_
  intro β α hβ hβα hα
  obtain ⟨hr, hm, -, -, -, -⟩ := fa_fac h1 hβ hβα hα
  have hA := fa_A_pos h1
  have hK := fa_K_pos h1
  obtain ⟨hp0, hp1, -, -, -, hl, hct, hab, hE, hI, -, hW, hQE, hQI, hCAE, hCAI, hCRE, -⟩ := h1
  have eθ : ∀ x, theta { P with muCT := x } = theta P := fun _ => rfl
  simp only [eθ] at hr hm hA hK hp0 hl hct hab hE ⊢
  have hL12 : lamTilde { P with muCT := x₁ } ≤ lamTilde { P with muCT := x₂ } := by
    simp only [lamTilde]
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith [mul_nonneg (mul_nonneg hl.le hab.le) (sub_nonneg.2 hx)]
  have key := fa_h_L hL1 hL12 hp0.le (mul_pos hK hE) hr hm
  rw [fa_Vd, fa_Vd]
  simp only [eθ, fa_c]
  linarith [mul_le_mul_of_nonneg_left key hA.le]

theorem fa_cl_9 :
    ∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with p := x₁ } : Params).Standing → ({ P with p := x₂ } : Params).Standing →
      x₁ ≤ x₂ →
      (∀ x ∈ Set.Icc x₁ x₂, ∀ a : ℝ, IsOptimal { P with p := x } a →
        psiE { P with p := x } a < 1) →
      IsOptimal { P with p := x₁ } a₁ → IsOptimal { P with p := x₂ } a₂ → a₁ ≤ a₂ := by
  intro P x₁ x₂ a₁ a₂ h1 h2 hx hψ ho1 ho2
  by_contra hlt
  have hlt' : a₂ < a₁ := lt_of_not_ge hlt
  have hψ2 := hψ x₂ ⟨hx, le_refl _⟩ a₂ ho2
  obtain ⟨α, hα1, hα2, hα3⟩ := fa_near h2 ho2.1 hlt' ho1.1.2 hψ2
  apply fa_local h1 ho1 ho2.1 hα1 hα2
  have hα : α ≤ 1 := le_trans hα2 ho1.1.2
  have hopt := ho2.2 α ⟨by linarith [ho2.1.1], hα⟩
  obtain ⟨hr, hm, -, -, hc1, hL⟩ := fa_fac h1 ho2.1.1 hα1 hα
  have hA := fa_A_pos h1
  have hK := fa_K_pos h1
  obtain ⟨hp0, hp1, -, -, -, hl, hct, hab, hE, hI, -, hW, hQE, hQI, hCAE, hCAI, hCRE, -⟩ := h1
  have eθ : ∀ x, theta { P with p := x } = theta P := fun _ => rfl
  have eL : ∀ x, lamTilde { P with p := x } = lamTilde P := fun _ => rfl
  have ec : ∀ x, fa_c { P with p := x } = lamTilde P * x / ((P.K : ℝ) * P.muE) :=
    fun _ => rfl
  suffices hs : V { P with p := x₁ } α - V { P with p := x₁ } a₂ ≤
      V { P with p := x₂ } α - V { P with p := x₂ } a₂ by linarith
  rw [fa_Vd, fa_Vd]
  simp only [eθ, eL, ec] at hr hm hc1 hL hα3 hA hK hp0 hp1 hE hI hW hQI hCAE hCAI hCRE ⊢
  have hc12 : lamTilde P * x₁ / ((P.K : ℝ) * P.muE) ≤ lamTilde P * x₂ / ((P.K : ℝ) * P.muE) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hx hL.le) (mul_pos hK hE).le
  have key := fa_h_dm hc1.le hc12 hr hm hα3
  have hB : 0 ≤ P.WTP * P.QI / P.muI + P.CAI := by
    have : 0 ≤ P.WTP * P.QI / P.muI := div_nonneg (mul_nonneg hW.le hQI) hI.le
    linarith
  have hEE : 0 ≤ P.CAE + P.CRE := by linarith
  linarith [mul_le_mul_of_nonneg_left key hA.le,
    mul_nonneg (mul_nonneg (sub_nonneg.2 hx) hL.le) (mul_nonneg hEE (sub_nonneg.2 hm)),
    mul_nonneg (mul_nonneg (sub_nonneg.2 hx) hL.le) (mul_nonneg hB (sub_nonneg.2 hα1.le))]

theorem fa_cl_10 :
    ∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with muE := x₁ } : Params).Standing → ({ P with muE := x₂ } : Params).Standing →
      x₁ ≤ x₂ →
      (∀ x ∈ Set.Icc x₁ x₂, ∀ a : ℝ, IsOptimal { P with muE := x } a →
        psiE { P with muE := x } a < 1) →
      IsOptimal { P with muE := x₁ } a₁ → IsOptimal { P with muE := x₂ } a₂ → a₂ ≤ a₁ := by
  intro P x₁ x₂ a₁ a₂ h1 h2 hx hψ ho1 ho2
  by_contra hlt
  have hlt' : a₁ < a₂ := lt_of_not_ge hlt
  have hψ1 := hψ x₁ ⟨le_refl _, hx⟩ a₁ ho1
  obtain ⟨α, hα1, hα2, hα3⟩ := fa_near h1 ho1.1 hlt' ho2.1.2 hψ1
  apply fa_local h2 ho2 ho1.1 hα1 hα2
  have hα : α ≤ 1 := le_trans hα2 ho2.1.2
  have hopt := ho1.2 α ⟨by linarith [ho1.1.1], hα⟩
  obtain ⟨hr, hm, -, -, hc2, hL⟩ := fa_fac h2 ho1.1.1 hα1 hα
  have hA := fa_A_pos h1
  have hK := fa_K_pos h1
  obtain ⟨hp0, hp1, -, -, -, hl, hct, hab, hE, hI, -, hW, hQE, hQI, hCAE, hCAI, hCRE, -⟩ := h1
  have eθ : ∀ x, theta { P with muE := x } = theta P := fun _ => rfl
  have eL : ∀ x, lamTilde { P with muE := x } = lamTilde P := fun _ => rfl
  have ec : ∀ x, fa_c { P with muE := x } = lamTilde P * P.p / ((P.K : ℝ) * x) :=
    fun _ => rfl
  suffices hs : V { P with muE := x₂ } α - V { P with muE := x₂ } a₁ ≤
      V { P with muE := x₁ } α - V { P with muE := x₁ } a₁ by linarith
  rw [fa_Vd, fa_Vd]
  simp only [eθ, eL, ec] at hr hm hc2 hL hα3 hA hK hp0 hE ⊢
  have hc21 : lamTilde P * P.p / ((P.K : ℝ) * x₂) ≤ lamTilde P * P.p / ((P.K : ℝ) * x₁) :=
    div_le_div_of_nonneg_left (mul_nonneg hL.le hp0.le) (mul_pos hK hE)
      (mul_le_mul_of_nonneg_left hx hK.le)
  have key := fa_h_dm hc2.le hc21 hr hm hα3
  linarith [mul_le_mul_of_nonneg_left key hA.le]

open FlexApproval.Statics in
theorem solution :
    -- (a) increasing in Q_E
    (∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with QE := x₁ } : Params).Standing → ({ P with QE := x₂ } : Params).Standing →
      x₁ ≤ x₂ → IsOptimal { P with QE := x₁ } a₁ → IsOptimal { P with QE := x₂ } a₂ → a₁ ≤ a₂) ∧
    -- (a) increasing in C_AE
    (∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with CAE := x₁ } : Params).Standing → ({ P with CAE := x₂ } : Params).Standing →
      x₁ ≤ x₂ → IsOptimal { P with CAE := x₁ } a₁ → IsOptimal { P with CAE := x₂ } a₂ → a₁ ≤ a₂) ∧
    -- (a) increasing in C_RE
    (∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with CRE := x₁ } : Params).Standing → ({ P with CRE := x₂ } : Params).Standing →
      x₁ ≤ x₂ → IsOptimal { P with CRE := x₁ } a₁ → IsOptimal { P with CRE := x₂ } a₂ → a₁ ≤ a₂) ∧
    -- (a) increasing in µ_I
    (∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with muI := x₁ } : Params).Standing → ({ P with muI := x₂ } : Params).Standing →
      x₁ ≤ x₂ → IsOptimal { P with muI := x₁ } a₁ → IsOptimal { P with muI := x₂ } a₂ → a₁ ≤ a₂) ∧
    -- (a) increasing in µ_AB
    (∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with muAB := x₁ } : Params).Standing → ({ P with muAB := x₂ } : Params).Standing →
      x₁ ≤ x₂ → IsOptimal { P with muAB := x₁ } a₁ → IsOptimal { P with muAB := x₂ } a₂ → a₁ ≤ a₂) ∧
    -- (b) decreasing in Q_I
    (∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with QI := x₁ } : Params).Standing → ({ P with QI := x₂ } : Params).Standing →
      x₁ ≤ x₂ → IsOptimal { P with QI := x₁ } a₁ → IsOptimal { P with QI := x₂ } a₂ → a₂ ≤ a₁) ∧
    -- (b) decreasing in C_AI
    (∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with CAI := x₁ } : Params).Standing → ({ P with CAI := x₂ } : Params).Standing →
      x₁ ≤ x₂ → IsOptimal { P with CAI := x₁ } a₁ → IsOptimal { P with CAI := x₂ } a₂ → a₂ ≤ a₁) ∧
    -- (b) decreasing in λ
    (∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with lam := x₁ } : Params).Standing → ({ P with lam := x₂ } : Params).Standing →
      x₁ ≤ x₂ → IsOptimal { P with lam := x₁ } a₁ → IsOptimal { P with lam := x₂ } a₂ → a₂ ≤ a₁) ∧
    -- (b) decreasing in µ_CT
    (∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with muCT := x₁ } : Params).Standing → ({ P with muCT := x₂ } : Params).Standing →
      x₁ ≤ x₂ → IsOptimal { P with muCT := x₁ } a₁ → IsOptimal { P with muCT := x₂ } a₂ → a₂ ≤ a₁) ∧
    -- (c) increasing in p, if ψ_E(α*) < 1 along the way
    (∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with p := x₁ } : Params).Standing → ({ P with p := x₂ } : Params).Standing →
      x₁ ≤ x₂ →
      (∀ x ∈ Set.Icc x₁ x₂, ∀ a : ℝ, IsOptimal { P with p := x } a →
        psiE { P with p := x } a < 1) →
      IsOptimal { P with p := x₁ } a₁ → IsOptimal { P with p := x₂ } a₂ → a₁ ≤ a₂) ∧
    -- (c) decreasing in µ_E, if ψ_E(α*) < 1 along the way
    (∀ (P : Params) (x₁ x₂ a₁ a₂ : ℝ),
      ({ P with muE := x₁ } : Params).Standing → ({ P with muE := x₂ } : Params).Standing →
      x₁ ≤ x₂ →
      (∀ x ∈ Set.Icc x₁ x₂, ∀ a : ℝ, IsOptimal { P with muE := x } a →
        psiE { P with muE := x } a < 1) →
      IsOptimal { P with muE := x₁ } a₁ → IsOptimal { P with muE := x₂ } a₂ → a₂ ≤ a₁) := by
  exact ⟨fa_cl_0, fa_cl_1, fa_cl_2, fa_cl_3, fa_cl_4, fa_cl_5, fa_cl_6, fa_cl_7, fa_cl_8, fa_cl_9, fa_cl_10⟩
