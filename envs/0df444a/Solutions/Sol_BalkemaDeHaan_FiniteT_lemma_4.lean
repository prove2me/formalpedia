-- Prove2me | solution 1 for BalkemaDeHaan.FiniteT.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:12:04.00484+00:00
-- url     : https://prove2.me/submissions/9895b832-eea9-47f0-adbe-f1c1c39830ec

import Mathlib
import Definitions.Def_BalkemaDeHaan_FiniteT_Pi0
import Definitions.Def_BalkemaDeHaan_FiniteT_ResidualLife

open MeasureTheory ProbabilityTheory

namespace BalkemaDeHaan.FiniteT

/-- `∫₀ˣ (1 + c s)⁻¹ ds`. -/
noncomputable def Ifun (x c : ℝ) : ℝ := ∫ s in (0 : ℝ)..x, (1 + c * s)⁻¹

/-- `∫₀ˣ s / (1 + c s)² ds`. -/
noncomputable def Jfun (x c : ℝ) : ℝ := ∫ s in (0 : ℝ)..x, s / (1 + c * s) ^ 2

lemma pos_on_d3 (x c : ℝ) (hx : 0 ≤ x) (h : 0 < 1 + c * x) :
    ∀ s ∈ Set.Icc 0 x, 0 < 1 + c * s := by
  intro s hs
  rcases le_or_gt 0 c with h0 | h0
  · nlinarith [hs.1]
  · nlinarith [hs.2]

lemma Ifun_eq_d3 (x c : ℝ) (hx : 0 ≤ x) (hc : c ≠ 0) (h : 0 < 1 + c * x) :
    Ifun x c = Real.log (1 + c * x) / c := by
  unfold Ifun
  have hpos := pos_on_d3 x c hx h
  have e : (fun s : ℝ => (1 + c * s)⁻¹) = fun s => (fun w : ℝ => w⁻¹) (c * s + 1) := by
    funext s; simp [add_comm]
  rw [e, intervalIntegral.integral_comp_mul_add (fun w : ℝ => w⁻¹) hc 1]
  rw [integral_inv]
  · simp only [mul_zero, zero_add, div_one, smul_eq_mul]
    rw [div_eq_inv_mul, add_comm]
  · rw [Set.mem_uIcc]
    push_neg
    constructor
    · intro h1; linarith
    · intro h1; linarith

lemma Ifun_zero_c_d3 (x : ℝ) : Ifun x 0 = x := by
  simp [Ifun]

lemma pi0_eq_exp_d3 (c x : ℝ) (hx : 0 < x) (h : 0 < 1 + c * x) :
    pi0 c x = 1 - Real.exp (-Ifun x c) := by
  unfold pi0
  rw [if_neg (not_lt.mpr hx.le)]
  by_cases hc : c = 0
  · subst hc; simp [Ifun_zero_c_d3]
  · rw [if_neg hc, Ifun_eq_d3 x c hx.le hc h]
    have hrpow : (1 + c * x) ^ (-1 / c) = Real.exp (-(Real.log (1 + c * x) / c)) := by
      rw [Real.rpow_def_of_pos h]; congr 1; ring
    by_cases hc' : 0 < c
    · rw [if_pos hc', hrpow]
    · rw [if_neg hc']
      have hcneg : c < 0 := lt_of_le_of_ne (not_lt.mp hc') hc
      have hxle : x ≤ |c|⁻¹ := by
        rw [abs_of_neg hcneg, ← one_div, le_div_iff₀ (neg_pos.mpr hcneg)]; linarith
      rw [if_pos hxle, hrpow]

lemma pi0_nonpos_x_d3 (c x : ℝ) (hx : x ≤ 0) : pi0 c x = 0 := by
  rcases hx.lt_or_eq with h | h
  · simp [pi0, h]
  · subst h
    unfold pi0
    simp

lemma pi0_eq_one_d3 (c x : ℝ) (hc : c < 0) (hx : 0 < x) (h : 1 + c * x ≤ 0) : pi0 c x = 1 := by
  unfold pi0
  rw [if_neg (not_lt.mpr hx.le), if_neg hc.ne, if_neg (not_lt.mpr hc.le)]
  by_cases hxle : x ≤ |c|⁻¹
  · rw [if_pos hxle]
    have h0 : 1 + c * x = 0 := by
      rw [abs_of_neg hc, ← one_div, le_div_iff₀ (neg_pos.mpr hc)] at hxle
      linarith
    rw [h0, Real.zero_rpow]
    · ring
    · have : 0 < -1 / c := div_pos_of_neg_of_neg (by norm_num) hc
      exact this.ne'
  · rw [if_neg hxle]

lemma pi0_mem_Icc_d3 (c x : ℝ) : 0 ≤ pi0 c x ∧ pi0 c x ≤ 1 := by
  unfold pi0
  by_cases hx : x < 0
  · simp [hx]
  · rw [if_neg hx]
    push Not at hx
    by_cases hc : c = 0
    · rw [if_pos hc]
      have h1 : Real.exp (-x) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
      have h2 : 0 < Real.exp (-x) := Real.exp_pos _
      constructor <;> linarith
    · rw [if_neg hc]
      by_cases hc' : 0 < c
      · rw [if_pos hc']
        have hb : 1 ≤ 1 + c * x := by nlinarith
        have h1 : (1 + c * x) ^ (-1 / c) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hb (by
            have : 0 < 1 / c := by positivity
            linarith [show -1 / c = -(1 / c) by ring])
        have h2 : 0 ≤ (1 + c * x) ^ (-1 / c) := Real.rpow_nonneg (by linarith) _
        constructor <;> linarith
      · rw [if_neg hc']
        have hcneg : c < 0 := lt_of_le_of_ne (not_lt.mp hc') hc
        by_cases hxle : x ≤ |c|⁻¹
        · rw [if_pos hxle]
          have hb0 : 0 ≤ 1 + c * x := by
            rw [abs_of_neg hcneg, ← one_div, le_div_iff₀ (neg_pos.mpr hcneg)] at hxle
            linarith
          have hb1 : 1 + c * x ≤ 1 := by nlinarith
          have he : 0 ≤ -1 / c := (div_pos_of_neg_of_neg (by norm_num) hcneg).le
          have h1 : (1 + c * x) ^ (-1 / c) ≤ 1 := Real.rpow_le_one hb0 hb1 he
          have h2 : 0 ≤ (1 + c * x) ^ (-1 / c) := Real.rpow_nonneg hb0 _
          constructor <;> linarith
        · rw [if_neg hxle]; norm_num

/-- Derivative of `c ↦ Ifun x c`. -/
lemma Ifun_hasDerivAt_d3 (x c₀ : ℝ) (hx : 0 < x) (h : 0 < 1 + c₀ * x) :
    HasDerivAt (fun c => Ifun x c) (-Jfun x c₀) c₀ := by
  set m := min 1 (1 + c₀ * x) with hm
  have hm0 : 0 < m := lt_min one_pos h
  set ε := m / (2 * x) with hε
  have hε0 : 0 < ε := by positivity
  have hlow : ∀ c ∈ Metric.ball c₀ ε, ∀ s ∈ Set.Icc 0 x, m / 2 ≤ 1 + c * s := by
    intro c hc s hs
    rw [Metric.mem_ball, Real.dist_eq] at hc
    have h1 : m ≤ 1 + c₀ * s := by
      rcases le_or_gt 0 c₀ with h0 | h0
      · exact le_trans (min_le_left _ _) (by nlinarith [hs.1])
      · exact le_trans (min_le_right _ _) (by nlinarith [hs.2])
    have h2 : |(c - c₀) * s| ≤ ε * x := by
      rw [abs_mul, abs_of_nonneg hs.1]
      exact mul_le_mul hc.le hs.2 hs.1 hε0.le
    have h3 : ε * x = m / 2 := by rw [hε]; field_simp
    have h4 := (abs_le.mp h2).1
    nlinarith
  have hcontF : ContinuousOn (fun s : ℝ => (1 + c₀ * s)⁻¹) (Set.Icc 0 x) :=
    (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).inv₀
      (fun s hs => (lt_of_lt_of_le (half_pos hm0) (hlow c₀ (Metric.mem_ball_self hε0) s hs)).ne')
  have hJ := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun c s => (1 + c * s)⁻¹) (F' := fun c s => -(s / (1 + c * s) ^ 2))
    (bound := fun _ => x / (m / 2) ^ 2) (μ := volume) (a := 0) (b := x)
    (Metric.ball_mem_nhds c₀ hε0) ?_ ?_ ?_ ?_ ?_ ?_
  · have := hJ.2
    unfold Ifun Jfun
    rw [intervalIntegral.integral_neg] at this
    exact this
  · filter_upwards with c
    exact Measurable.aestronglyMeasurable (by fun_prop)
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx.le]
    exact hcontF
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards with s
    intro hs c hc
    rw [Set.uIoc_of_le hx.le] at hs
    have hl := hlow c hc s ⟨hs.1.le, hs.2⟩
    have hp : 0 < 1 + c * s := lt_of_lt_of_le (half_pos hm0) hl
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hs.1.le (sq_nonneg _))]
    exact div_le_div₀ hx.le hs.2 (by positivity) (pow_le_pow_left₀ (half_pos hm0).le hl 2)
  · exact intervalIntegrable_const
  · filter_upwards with s
    intro hs c hc
    rw [Set.uIoc_of_le hx.le] at hs
    have hl := hlow c hc s ⟨hs.1.le, hs.2⟩
    have hne : 1 + c * s ≠ 0 := (lt_of_lt_of_le (half_pos hm0) hl).ne'
    have hd : HasDerivAt (fun c => 1 + c * s) s c := by
      simpa using ((hasDerivAt_id c).mul_const s).const_add 1
    have := hd.inv hne
    rw [neg_div] at this
    exact this

lemma pi0_hasDerivAt_d3 (c₀ x : ℝ) (hx : 0 < x) (h : 0 < 1 + c₀ * x) :
    HasDerivAt (fun c => pi0 c x) (-(Real.exp (-Ifun x c₀) * Jfun x c₀)) c₀ := by
  have hI := Ifun_hasDerivAt_d3 x c₀ hx h
  have hexp : HasDerivAt (fun c => 1 - Real.exp (-Ifun x c))
      (0 - Real.exp (-Ifun x c₀) * (-(-Jfun x c₀))) c₀ :=
    (hasDerivAt_const c₀ (1 : ℝ)).sub hI.neg.exp
  have hev : (fun c => pi0 c x) =ᶠ[nhds c₀] (fun c => 1 - Real.exp (-Ifun x c)) := by
    have hopen : IsOpen {c : ℝ | 0 < 1 + c * x} := isOpen_lt continuous_const (by fun_prop)
    filter_upwards [hopen.mem_nhds h] with c hc
    exact pi0_eq_exp_d3 c x hx hc
  refine (hexp.congr_of_eventuallyEq hev).congr_deriv ?_
  ring

lemma Jfun_nonneg_d3 (x c : ℝ) (hx : 0 ≤ x) : 0 ≤ Jfun x c :=
  intervalIntegral.integral_nonneg hx (fun s hs => div_nonneg hs.1 (sq_nonneg _))

lemma Ifun_hasDerivAt_x_d3 (c u : ℝ) (hu : 0 ≤ u) (h : 0 < 1 + c * u) :
    HasDerivAt (fun v => Ifun v c) ((1 + c * u)⁻¹) u := by
  unfold Ifun
  have hopen : IsOpen {s : ℝ | 0 < 1 + c * s} := isOpen_lt continuous_const (by fun_prop)
  have hcont : ContinuousOn (fun s : ℝ => (1 + c * s)⁻¹) {s | 0 < 1 + c * s} :=
    (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).inv₀
      (fun s hs => (show (0 : ℝ) < 1 + c * s from hs).ne')
  apply intervalIntegral.integral_hasDerivAt_right
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hu]
    exact hcont.mono (fun s hs => pos_on_d3 u c hu h s hs)
  · exact hcont.stronglyMeasurableAtFilter hopen u h
  · exact hcont.continuousAt (hopen.mem_nhds h)

lemma Jfun_hasDerivAt_x_d3 (c u : ℝ) (hu : 0 ≤ u) (h : 0 < 1 + c * u) :
    HasDerivAt (fun v => Jfun v c) (u / (1 + c * u) ^ 2) u := by
  unfold Jfun
  have hopen : IsOpen {s : ℝ | 0 < 1 + c * s} := isOpen_lt continuous_const (by fun_prop)
  have hcont : ContinuousOn (fun s : ℝ => s / (1 + c * s) ^ 2) {s | 0 < 1 + c * s} :=
    continuousOn_id.div ((continuousOn_const.add (continuousOn_const.mul continuousOn_id)).pow 2)
      (fun s hs => pow_ne_zero _ (show (0 : ℝ) < 1 + c * s from hs).ne')
  apply intervalIntegral.integral_hasDerivAt_right
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hu]
    exact hcont.mono (fun s hs => pos_on_d3 u c hu h s hs)
  · exact hcont.stronglyMeasurableAtFilter hopen u h
  · exact hcont.continuousAt (hopen.mem_nhds h)

lemma Ifun_ge_d3 (c u : ℝ) (hu : 0 ≤ u) (h : 0 < 1 + c * u) (K : ℝ)
    (hK : ∀ s ∈ Set.Icc 0 u, K ≤ (1 + c * s)⁻¹) : K * u ≤ Ifun u c := by
  unfold Ifun
  have hcont : ContinuousOn (fun s : ℝ => (1 + c * s)⁻¹) (Set.Icc 0 u) :=
    (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).inv₀
      (fun s hs => (pos_on_d3 u c hu h s hs).ne')
  have := intervalIntegral.integral_mono_on hu
    (intervalIntegrable_const (μ := volume) (a := 0) (b := u) (c := K))
    (hcont.intervalIntegrable_of_Icc hu) hK
  rw [intervalIntegral.integral_const] at this
  simp only [sub_zero, smul_eq_mul] at this
  linarith

lemma key_ineq_d3 (c u : ℝ) (hc : -1 ≤ c) (hu : 0 ≤ u) (h : 0 < 1 + c * u) :
    u ≤ Real.exp (Ifun u c) * (1 + c * u) := by
  rcases le_or_gt 0 c with h0 | h0
  · have hI : (1 + c * u)⁻¹ * u ≤ Ifun u c := by
      apply Ifun_ge_d3 c u hu h
      intro s hs
      apply inv_anti₀ (pos_on_d3 u c hu h s hs)
      nlinarith [hs.2]
    have he : 1 + Ifun u c ≤ Real.exp (Ifun u c) := by linarith [Real.add_one_le_exp (Ifun u c)]
    have h2 : (1 + Ifun u c) * (1 + c * u) ≤ Real.exp (Ifun u c) * (1 + c * u) :=
      mul_le_mul_of_nonneg_right he h.le
    have h3 : (1 + c * u)⁻¹ * u * (1 + c * u) = u := by field_simp
    nlinarith
  · have hI : 1 * u ≤ Ifun u c := by
      apply Ifun_ge_d3 c u hu h
      intro s hs
      rw [le_inv_comm₀ one_pos (pos_on_d3 u c hu h s hs), inv_one]
      nlinarith [hs.1]
    have hcl : Ifun u c = Real.log (1 + c * u) / c := Ifun_eq_d3 u c hu h0.ne h
    have hcne : c ≠ 0 := h0.ne
    have hlog : Real.log (1 + c * u) = c * Ifun u c := by
      rw [hcl]; field_simp
    have e : Real.exp (Ifun u c) * (1 + c * u) = Real.exp ((1 + c) * Ifun u c) := by
      rw [← Real.exp_log h, ← Real.exp_add, hlog]; congr 1; ring
    rw [e]
    have := Real.add_one_le_exp ((1 + c) * Ifun u c)
    have h1c : 0 ≤ 1 + c := by linarith
    nlinarith

lemma J_lt_exp_d3 (c x : ℝ) (hc : -1 ≤ c) (hx : 0 < x) (h : 0 < 1 + c * x) :
    Jfun x c < Real.exp (Ifun x c) := by
  have hpos := pos_on_d3 x c hx.le h
  have hder : ∀ u ∈ Set.Icc 0 x, HasDerivAt (fun v => Real.exp (Ifun v c) - Jfun v c)
      (Real.exp (Ifun u c) * (1 + c * u)⁻¹ - u / (1 + c * u) ^ 2) u :=
    fun u hu => ((Ifun_hasDerivAt_x_d3 c u hu.1 (hpos u hu)).exp).sub
      (Jfun_hasDerivAt_x_d3 c u hu.1 (hpos u hu))
  have hmono : MonotoneOn (fun v => Real.exp (Ifun v c) - Jfun v c) (Set.Icc 0 x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
    · exact fun u hu => (hder u hu).continuousAt.continuousWithinAt
    · exact fun u hu => (hder u (interior_subset hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      have hu' : u ∈ Set.Icc 0 x := ⟨hu.1.le, hu.2.le⟩
      rw [(hder u hu').deriv]
      have hp := hpos u hu'
      have key := key_ineq_d3 c u hc hu.1.le hp
      rw [sub_nonneg, div_le_iff₀ (by positivity)]
      calc u ≤ Real.exp (Ifun u c) * (1 + c * u) := key
        _ = Real.exp (Ifun u c) * (1 + c * u)⁻¹ * (1 + c * u) ^ 2 := by field_simp
  have h0 : Real.exp (Ifun 0 c) - Jfun 0 c = 1 := by simp [Ifun, Jfun]
  have := hmono ⟨le_rfl, hx.le⟩ ⟨hx.le, le_rfl⟩ hx.le
  simp only at this
  rw [h0] at this
  linarith

/-- The derivative bound: `|d| ≤ 1` with `d = -(exp(-I) J)`. -/
lemma deriv_bound_d3 (c x : ℝ) (hc : -1 ≤ c) (hx : 0 < x) (h : 0 < 1 + c * x) :
    0 ≤ Real.exp (-Ifun x c) * Jfun x c ∧ Real.exp (-Ifun x c) * Jfun x c < 1 := by
  constructor
  · exact mul_nonneg (Real.exp_pos _).le (Jfun_nonneg_d3 x c hx.le)
  · rw [Real.exp_neg, inv_mul_eq_div, div_lt_one (Real.exp_pos _)]
    exact J_lt_exp_d3 c x hc hx h

theorem lemma_4_core (c x : ℝ) (hc : -1 < c) (hx : x ≠ 0) (hcx : c * x ≠ -1) :
    ∃ d : ℝ, HasDerivAt (fun c' : ℝ => pi0 c' x) d c ∧ 0 ≤ -d ∧ -d < 1 := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · refine ⟨0, ?_, by simp, by simp⟩
    have e : (fun c' : ℝ => pi0 c' x) = fun _ => 0 := by
      funext c'; exact pi0_nonpos_x_d3 c' x hneg.le
    rw [e]; exact hasDerivAt_const _ _
  · rcases lt_or_gt_of_ne hcx with hlt | hgt
    · refine ⟨0, ?_, by simp, by simp⟩
      have hopen : IsOpen {c' : ℝ | c' * x < -1} := isOpen_lt (by fun_prop) continuous_const
      have hev : (fun c' => pi0 c' x) =ᶠ[nhds c] (fun _ => (1 : ℝ)) := by
        filter_upwards [hopen.mem_nhds hlt] with c' hc'
        have hc'neg : c' < 0 := by nlinarith
        exact pi0_eq_one_d3 c' x hc'neg hpos (by linarith [show c' * x < -1 from hc'])
      exact (hasDerivAt_const c (1 : ℝ)).congr_of_eventuallyEq hev
    · have h : 0 < 1 + c * x := by linarith
      obtain ⟨h1, h2⟩ := deriv_bound_d3 c x hc.le hpos h
      exact ⟨_, pi0_hasDerivAt_d3 c x hpos h, by simpa using h1, by simpa using h2⟩

/-- Mean value estimate on `[p, q]`. -/
lemma pi0_mvt_d3 (x p q : ℝ) (hx : 0 < x) (hp : -1 ≤ p) (hpq : p ≤ q) (h : 0 < 1 + p * x) :
    |pi0 q x - pi0 p x| ≤ q - p := by
  have hder : ∀ c ∈ Set.Icc p q, HasDerivWithinAt (fun c => pi0 c x)
      (-(Real.exp (-Ifun x c) * Jfun x c)) (Set.Icc p q) c := by
    intro c hc
    have hc' : 0 < 1 + c * x := by nlinarith [hc.1]
    exact (pi0_hasDerivAt_d3 c x hx hc').hasDerivWithinAt
  have hbound : ∀ c ∈ Set.Icc p q, ‖-(Real.exp (-Ifun x c) * Jfun x c)‖ ≤ 1 := by
    intro c hc
    have hc' : 0 < 1 + c * x := by nlinarith [hc.1]
    obtain ⟨h1, h2⟩ := deriv_bound_d3 c x (by linarith [hc.1]) hx hc'
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg h1]
    exact h2.le
  have := (convex_Icc p q).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound
    ⟨le_rfl, hpq⟩ ⟨hpq, le_rfl⟩
  simp only [Real.norm_eq_abs, one_mul] at this
  rw [abs_of_nonneg (show (0 : ℝ) ≤ q - p by linarith)] at this
  exact this

theorem pi0_lipschitz_core (c : ℝ) (hc : 0 ≤ c) (c₀ x : ℝ) :
    |pi0 c x - pi0 c₀ x| ≤ |c - c₀| := by
  rcases le_or_gt x 0 with hx | hx
  · rw [pi0_nonpos_x_d3 c x hx, pi0_nonpos_x_d3 c₀ x hx]; simp
  obtain ⟨ha0, ha1⟩ := pi0_mem_Icc_d3 c x
  obtain ⟨hb0, hb1⟩ := pi0_mem_Icc_d3 c₀ x
  rcases lt_or_ge c₀ (-1) with hc₀ | hc₀
  · rw [abs_of_pos (show (0 : ℝ) < c - c₀ by linarith)]
    rw [abs_le]; constructor <;> linarith
  rcases le_or_gt c₀ c with hle | hlt
  · -- c₀ ≤ c
    rw [abs_of_nonneg (show (0 : ℝ) ≤ c - c₀ by linarith)]
    by_cases h : 0 < 1 + c₀ * x
    · exact pi0_mvt_d3 x c₀ c hx hc₀ hle h
    · push Not at h
      have hc₀neg : c₀ < 0 := by nlinarith
      rw [pi0_eq_one_d3 c₀ x hc₀neg hx h]
      -- c' = -1/x
      set c' := -1 / x with hc'
      have hc'x : 1 + c' * x = 0 := by rw [hc', div_mul_cancel₀ _ hx.ne']; ring
      have hc'neg : c' < 0 := by rw [hc']; exact div_neg_of_neg_of_pos (by norm_num) hx
      have hc₀c' : c₀ ≤ c' := by
        rw [hc', le_div_iff₀ hx]; linarith
      have hc'1 : -1 ≤ c' := le_trans hc₀ hc₀c'
      -- for c'' ∈ (c', 0): 1 - pi0 c x ≤ (1 + c'' x)^(-1/c'') + (c - c'')
      have hev : ∀ᶠ c'' in nhdsWithin c' (Set.Ioi c'),
          1 - pi0 c x ≤ (1 + c'' * x) ^ (-1 / c'') + (c - c'') := by
        have h1 : ∀ᶠ c'' in nhdsWithin c' (Set.Ioi c'), c'' < 0 :=
          eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hc'neg)
        filter_upwards [self_mem_nhdsWithin, h1] with c'' hgt hlt0
        have hgt' : c' < c'' := hgt
        have hpos'' : 0 < 1 + c'' * x := by nlinarith
        have hm := pi0_mvt_d3 x c'' c hx (by linarith) (by linarith) hpos''
        have hxle : x ≤ |c''|⁻¹ := by
          rw [abs_of_neg hlt0, ← one_div, le_div_iff₀ (neg_pos.mpr hlt0)]; linarith
        have hval : pi0 c'' x = 1 - (1 + c'' * x) ^ (-1 / c'') := by
          unfold pi0
          rw [if_neg (not_lt.mpr hx.le), if_neg hlt0.ne, if_neg (not_lt.mpr hlt0.le), if_pos hxle]
        rw [hval] at hm
        have := (abs_le.mp hm).1
        linarith
      have hT : Filter.Tendsto (fun c'' => (1 + c'' * x) ^ (-1 / c'') + (c - c''))
          (nhdsWithin c' (Set.Ioi c')) (nhds (0 + (c - c'))) := by
        apply Filter.Tendsto.add
        · have hcont : ContinuousAt (fun c'' => (1 + c'' * x) ^ (-1 / c'')) c' := by
            have hp : ContinuousAt (fun c'' : ℝ => (1 + c'' * x, -1 / c'')) c' :=
              (continuousAt_const.add (continuousAt_id.mul continuousAt_const)).prodMk
                (continuousAt_const.div continuousAt_id hc'neg.ne)
            have hr := Real.continuousAt_rpow (1 + c' * x, -1 / c') (Or.inr (by
              show 0 < -1 / c'
              exact div_pos_of_neg_of_neg (by norm_num) hc'neg))
            exact ContinuousAt.comp (f := fun c'' : ℝ => (1 + c'' * x, -1 / c''))
              (g := fun p : ℝ × ℝ => p.1 ^ p.2) hr hp
          have hval : (1 + c' * x) ^ (-1 / c') = 0 := by
            rw [hc'x, Real.zero_rpow]
            exact (div_pos_of_neg_of_neg (by norm_num) hc'neg).ne'
          rw [← hval]
          exact hcont.continuousWithinAt
        · exact (tendsto_const_nhds.sub Filter.tendsto_id).mono_left nhdsWithin_le_nhds
      have hle : 1 - pi0 c x ≤ 0 + (c - c') := ge_of_tendsto hT hev
      rw [abs_of_nonpos (show pi0 c x - 1 ≤ 0 by linarith)]
      linarith
  · -- c < c₀ : use MVT on [c, c₀]
    rw [abs_of_neg (show c - c₀ < 0 by linarith)]
    have := pi0_mvt_d3 x c c₀ hx (by linarith) hlt.le (by nlinarith)
    rw [abs_sub_comm] at this
    linarith

end BalkemaDeHaan.FiniteT

open BalkemaDeHaan.FiniteT


theorem solution (c x : ℝ) (hc : -1 < c) (hx : x ≠ 0) (hcx : c * x ≠ -1) :
    ∃ d : ℝ, HasDerivAt (fun c' : ℝ => pi0 c' x) d c ∧ 0 ≤ -d ∧ -d < 1 := by
  exact lemma_4_core c x hc hx hcx
