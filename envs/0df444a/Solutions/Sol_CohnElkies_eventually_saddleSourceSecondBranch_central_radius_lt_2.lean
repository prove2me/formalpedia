-- Prove2me | solution 2 for CohnElkies.eventually_saddleSourceSecondBranch_central_radius_lt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:39:28.381074+00:00
-- url     : https://prove2.me/submissions/46b52619-62a8-4dfc-a0c9-3add4ea93e05

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
theorem h48_pw {ε ℓ u a : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (ha : 0 < a)
    (hulower : -1 ≤ u)
    (huupper : u ≤ 1 + ε / 2)
    (hmargin : 0 ≤ shortMargin ε a) :
    ℓ * (-shortShellDensity ε a) * Real.cosh (u * a) ≤
      (1 - 4 * ε) *
        upperGammaMeasureDensity ℓ (1 + u) a := by
  unfold shortShellDensity upperGammaMeasureDensity shortMargin
  unfold shortMargin at hmargin
  set m : ℝ := 1 - 10 * ε * (1 + a) with hm
  have hm1 : m ≤ 1 - 10 * ε := by nlinarith
  have hea := Real.exp_pos a
  have hEε : 1 ≤ Real.exp (ε * a) := Real.one_le_exp (by positivity)
  -- (1 - ε a) e^{ε a} ≤ 1
  have hx : (1 - ε * a) * Real.exp (ε * a) ≤ 1 := by
    have h := Real.add_one_le_exp (-(ε * a))
    have : Real.exp (-(ε * a)) * Real.exp (ε * a) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (ε * a)]
  have hmE : m * Real.exp (ε * a) ≤ 1 - 10 * ε := by
    have : m * Real.exp (ε * a) = (1 - 10 * ε * a) * Real.exp (ε * a) - 10 * ε * Real.exp (ε * a) := by
      rw [hm]; ring
    rw [this]
    have h2 : (1 - 10 * ε * a) * Real.exp (ε * a) ≤ (1 - ε * a) * Real.exp (ε * a) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; nlinarith
    nlinarith
  have hup : Real.exp ((2 * u - 1) * a) ≤ Real.exp a * Real.exp (ε * a) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
  have hinner : m * (Real.exp ((2 * u - 1) * a) + Real.exp (-a)) ≤
      (1 - 4 * ε) * (Real.exp a + Real.exp (-a)) := by
    have hEna := Real.exp_pos (-a)
    have h3 : m * Real.exp ((2 * u - 1) * a) ≤ m * (Real.exp a * Real.exp (ε * a)) :=
      mul_le_mul_of_nonneg_left hup hmargin
    have h4 : m * (Real.exp a * Real.exp (ε * a)) ≤ (1 - 10 * ε) * Real.exp a := by
      have := mul_le_mul_of_nonneg_left hmE hea.le
      linarith [this]
    nlinarith
  have k1 : Real.exp (-2 * a) * Real.exp (u * a) =
      Real.exp (-(1 + u) * a) * Real.exp ((2 * u - 1) * a) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have k2 : Real.exp (-2 * a) * Real.exp (-(u * a)) =
      Real.exp (-(1 + u) * a) * Real.exp (-a) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have key : m * Real.exp (-2 * a) * Real.cosh (u * a) ≤
      (1 - 4 * ε) * Real.exp (-(1 + u) * a) * Real.cosh a := by
    rw [Real.cosh_eq, Real.cosh_eq]
    have e : m * Real.exp (-2 * a) * ((Real.exp (u * a) + Real.exp (-(u * a))) / 2) =
        Real.exp (-(1 + u) * a) * (m * (Real.exp ((2 * u - 1) * a) + Real.exp (-a))) / 2 := by
      rw [show m * Real.exp (-2 * a) * ((Real.exp (u * a) + Real.exp (-(u * a))) / 2) =
        m * (Real.exp (-2 * a) * Real.exp (u * a) + Real.exp (-2 * a) * Real.exp (-(u * a))) / 2 by ring,
        k1, k2]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hinner (Real.exp_pos (-(1 + u) * a)).le
    nlinarith
  -- denominator bound
  have hden_pos : 0 < 1 - Real.exp (-(2 * a / ℓ)) := by
    have : Real.exp (-(2 * a / ℓ)) < Real.exp 0 := Real.exp_lt_exp.mpr (show -(2 * a / ℓ) < 0 by
      have : 0 < 2 * a / ℓ := by positivity
      linarith)
    rw [Real.exp_zero] at this
    linarith
  have hden_le : 1 - Real.exp (-(2 * a / ℓ)) ≤ 2 * a / ℓ := by
    have := Real.add_one_le_exp (-(2 * a / ℓ)); linarith
  have hcosh := Real.cosh_pos a
  have h14 : 0 ≤ 1 - 4 * ε := by linarith
  -- assemble
  have lhs_eq : ℓ * -(-(m * Real.exp (-2 * a) / (2 * a ^ 2 * Real.cosh a))) * Real.cosh (u * a) =
      ℓ / (2 * a ^ 2) * (m * Real.exp (-2 * a) * Real.cosh (u * a) / Real.cosh a) := by
    field_simp
  rw [lhs_eq, mul_div_assoc' (1 - 4 * ε)]
  calc ℓ / (2 * a ^ 2) * (m * Real.exp (-2 * a) * Real.cosh (u * a) / Real.cosh a)
      ≤ ℓ / (2 * a ^ 2) * ((1 - 4 * ε) * Real.exp (-(1 + u) * a)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_iff₀ hcosh]; exact key
    _ = (1 - 4 * ε) * Real.exp (-(1 + u) * a) / (a * (2 * a / ℓ)) := by
        field_simp
    _ ≤ (1 - 4 * ε) * Real.exp (-(1 + u) * a) / (a * (1 - Real.exp (-(2 * a / ℓ)))) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hden_le ha.le

theorem h48_dens_nonneg (ℓ η : ℝ) {a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) :
    0 ≤ upperGammaMeasureDensity ℓ η a := by
  unfold upperGammaMeasureDensity
  have : Real.exp (-(2 * a / ℓ)) < 1 := by
    have h := Real.exp_lt_exp.mpr (show -(2 * a / ℓ) < 0 by
      have : 0 < 2 * a / ℓ := by positivity
      linarith)
    rwa [Real.exp_zero] at h
  have : 0 < 1 - Real.exp (-(2 * a / ℓ)) := by linarith
  positivity

theorem h48_sq_dens_le (ℓ η : ℝ) {a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) :
    a ^ 2 * upperGammaMeasureDensity ℓ η a ≤ (ℓ / 2 + a) * Real.exp (-η * a) := by
  unfold upperGammaMeasureDensity
  set x : ℝ := 2 * a / ℓ with hx
  have hxpos : 0 < x := by positivity
  have hE : Real.exp (-x) * (1 + x) ≤ 1 := by
    have h1 := Real.add_one_le_exp x
    have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-x)]
  have hden : x / (1 + x) ≤ 1 - Real.exp (-x) := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hdpos : 0 < 1 - Real.exp (-x) := lt_of_lt_of_le (by positivity) hden
  have he := Real.exp_pos (-η * a)
  rw [show a ^ 2 * (Real.exp (-η * a) / (a * (1 - Real.exp (-x)))) =
    a * Real.exp (-η * a) / (1 - Real.exp (-x)) by field_simp]
  rw [div_le_iff₀ hdpos]
  have : (ℓ / 2 + a) * (x / (1 + x)) = a := by
    rw [hx]; field_simp
  calc a * Real.exp (-η * a) = Real.exp (-η * a) * ((ℓ / 2 + a) * (x / (1 + x))) := by rw [this]; ring
    _ ≤ Real.exp (-η * a) * ((ℓ / 2 + a) * (1 - Real.exp (-x))) := by
        gcongr
    _ = _ := by ring

theorem h48_dens_contOn (ℓ η : ℝ) (hℓ : 0 < ℓ) :
    ContinuousOn (upperGammaMeasureDensity ℓ η) (Set.Ioi 0) := by
  unfold upperGammaMeasureDensity
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro a ha
  have ha' : (0:ℝ) < a := ha
  have : Real.exp (-(2 * a / ℓ)) < 1 := by
    have h := Real.exp_lt_exp.mpr (show -(2 * a / ℓ) < 0 by
      have : 0 < 2 * a / ℓ := by positivity
      linarith)
    rwa [Real.exp_zero] at h
  have : 0 < 1 - Real.exp (-(2 * a / ℓ)) := by linarith
  positivity

theorem h48_majorant_int (ℓ η : ℝ) (hη : 0 < η) :
    IntegrableOn (fun a : ℝ => (ℓ / 2 + a) * Real.exp (-η * a)) (Set.Ioi 0) := by
  have h0 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (0 : ℝ)) (p := 1) (b := η)
    (by norm_num) one_pos hη
  have h1 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (1 : ℝ)) (p := 1) (b := η)
    (by norm_num) one_pos hη
  have := (h0.const_mul (ℓ / 2)).add h1
  refine IntegrableOn.congr_fun this (fun a ha => ?_) measurableSet_Ioi
  simp only [Pi.add_apply, Real.rpow_zero, Real.rpow_one]
  ring

theorem h48_int_var (ℓ η : ℝ) (hℓ : 0 < ℓ) (hη : 0 < η) :
    IntegrableOn (fun a : ℝ => a ^ 2 * upperGammaMeasureDensity ℓ η a) (Set.Ioi 0) := by
  refine (h48_majorant_int ℓ η hη).mono' ?_ ?_
  · exact ((continuousOn_id.pow 2).mul (h48_dens_contOn ℓ η hℓ)).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun a ha => ?_))
    have ha' : (0:ℝ) < a := ha
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (h48_dens_nonneg ℓ η hℓ ha'))]
    exact h48_sq_dens_le ℓ η hℓ ha'

theorem h48_int_damp (ℓ η T : ℝ) (hℓ : 0 < ℓ) (hη : 0 < η) :
    IntegrableOn (fun a : ℝ => upperGammaDampingIntegrand ℓ η T a) (Set.Ioi 0) := by
  refine ((h48_int_var ℓ η hℓ hη).const_mul (T ^ 2 / 2)).mono' ?_ ?_
  · unfold upperGammaDampingIntegrand
    exact ((Continuous.continuousOn (by fun_prop)).mul (h48_dens_contOn ℓ η hℓ)).aestronglyMeasurable
      measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun a ha => ?_))
    have ha' : (0:ℝ) < a := ha
    unfold upperGammaDampingIntegrand
    have hd := h48_dens_nonneg ℓ η hℓ ha'
    have hc : 0 ≤ 1 - Real.cos (a * T) := by linarith [Real.cos_le_one (a * T)]
    have hc2 : 1 - Real.cos (a * T) ≤ (a * T) ^ 2 / 2 := by
      have := Real.one_sub_sq_div_two_le_cos (x := a * T); linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc hd)]
    calc (1 - Real.cos (a * T)) * upperGammaMeasureDensity ℓ η a
        ≤ (a * T) ^ 2 / 2 * upperGammaMeasureDensity ℓ η a := mul_le_mul_of_nonneg_right hc2 hd
      _ = T ^ 2 / 2 * (a ^ 2 * upperGammaMeasureDensity ℓ η a) := by ring

theorem h48_gvar_ge (ℓ η : ℝ) (hℓ : 0 < ℓ) (hη : 0 < η) :
    1 / (2 * η) ≤ upperGammaVariance ℓ η := by
  unfold upperGammaVariance
  have hexp : IntegrableOn (fun a : ℝ => ℓ / 2 * Real.exp (-η * a)) (Set.Ioi 0) := by
    have h0 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (0 : ℝ)) (p := 1) (b := η)
      (by norm_num) one_pos hη
    simp only [Real.rpow_zero, Real.rpow_one, one_mul] at h0
    exact h0.const_mul _
  have hle : (∫ a in Set.Ioi (0:ℝ), ℓ / 2 * Real.exp (-η * a)) ≤
      ∫ a in Set.Ioi (0:ℝ), a ^ 2 * upperGammaMeasureDensity ℓ η a := by
    apply MeasureTheory.setIntegral_mono_on hexp (h48_int_var ℓ η hℓ hη) measurableSet_Ioi
    intro a ha
    have ha' : (0:ℝ) < a := ha
    unfold upperGammaMeasureDensity
    have hx : 1 - Real.exp (-(2 * a / ℓ)) ≤ 2 * a / ℓ := by
      have := Real.add_one_le_exp (-(2 * a / ℓ)); linarith
    have hpos : 0 < 1 - Real.exp (-(2 * a / ℓ)) := by
      have h := Real.exp_lt_exp.mpr (show -(2 * a / ℓ) < 0 by
        have : 0 < 2 * a / ℓ := by positivity
        linarith)
      rw [Real.exp_zero] at h; linarith
    have he := Real.exp_pos (-η * a)
    rw [show a ^ 2 * (Real.exp (-η * a) / (a * (1 - Real.exp (-(2 * a / ℓ))))) =
      a * Real.exp (-η * a) / (1 - Real.exp (-(2 * a / ℓ))) by field_simp]
    rw [le_div_iff₀ hpos]
    calc ℓ / 2 * Real.exp (-η * a) * (1 - Real.exp (-(2 * a / ℓ)))
        ≤ ℓ / 2 * Real.exp (-η * a) * (2 * a / ℓ) := by gcongr
      _ = a * Real.exp (-η * a) := by field_simp
  rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (by linarith) 0] at hle
  have hl : 0 < ℓ⁻¹ := inv_pos.mpr hℓ
  have := mul_le_mul_of_nonneg_left hle hl.le
  calc 1 / (2 * η) = ℓ⁻¹ * (ℓ / 2 * (-Real.exp (-η * 0) / -η)) := by
        simp; field_simp
    _ ≤ _ := this
theorem h48_margin_ev : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ a ∈ Set.Icc (shortCutoff ε) (shortEndpoint ε), 0 ≤ shortMargin ε a := by
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 / 160000 by norm_num)] with ε hε
  intro a ha
  obtain ⟨hε0, hε1⟩ := hε
  set t := Real.sqrt ε with ht
  have ht0 : 0 < t := Real.sqrt_pos.mpr hε0
  have htt : t ^ 2 = ε := Real.sq_sqrt hε0.le
  have ht1 : t < 1 / 400 := by
    rw [ht, Real.sqrt_lt' (by norm_num)]; norm_num; linarith
  have hlog : Real.log (1 / ε) ≤ 2 / t := by
    have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (show (0:ℝ) < 1 / ε by positivity))
    rw [Real.log_sqrt (by positivity)] at h1
    have : Real.sqrt (1 / ε) = 1 / t := by rw [ht, Real.sqrt_div' _ hε0.le, Real.sqrt_one]
    rw [this] at h1
    have : 2 / t = 2 * (1 / t) := by ring
    linarith
  have haE : a ≤ 20 / t := by
    have := ha.2; unfold shortEndpoint at this
    have : 10 * Real.log (1 / ε) ≤ 20 / t := by
      have h2 : 10 * (2 / t) = 20 / t := by ring
      linarith
    linarith
  unfold shortMargin
  have : 10 * ε * (1 + a) ≤ 10 * t ^ 2 + 200 * t := by
    rw [← htt]
    have h3 : 10 * t ^ 2 * (1 + a) ≤ 10 * t ^ 2 * (1 + 20 / t) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h4 : 10 * t ^ 2 * (1 + 20 / t) = 10 * t ^ 2 + 200 * t := by field_simp; ring
    linarith
  nlinarith

theorem h48_net_ev : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ δ : ℝ, ε / 2 ≤ δ →
        (99 / 100 : ℝ) *
            upperPositiveShellVariance ε δ ≤
          upperNetShellVariance ε δ ∧
        upperNetShellVariance ε δ ≤
          upperPositiveShellVariance ε δ := by
  filter_upwards [self_mem_nhdsWithin, h48_margin_ev, eventually_upper_shortCutoff_le_shortEndpoint,
    Ioo_mem_nhdsGT (show (0:ℝ) < 1 / 50 by norm_num)]
    with ε hε hmargin horder hε40
  have hε0 : 0 < ε := hε
  intro δ hδ
  have hδ0 : 0 < δ := by linarith
  have hc0 : 0 < shortCutoff ε := by unfold shortCutoff; positivity
  set E := shortEndpoint ε with hE
  set L := shellLocation ε with hL
  set w := shellWeight ε with hw
  set x : ℝ := 1 / ε with hx
  have hx40 : 50 < x := by rw [hx, lt_div_iff₀ hε0]; linarith [hε40.2]
  have hx0 : 0 < x := by linarith
  have hεx : ε * x = 1 := by rw [hx]; field_simp
  have hLx : L = x ^ 3 := by rw [hL, hx]; unfold shellLocation; field_simp
  have hE0 : 0 < E := hc0.trans_le horder
  -- E ≤ 10x/3
  have hlog : Real.log x ≤ 2 * Real.sqrt x := by
    have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx0)
    rw [Real.log_sqrt hx0.le] at h1; linarith
  have hsqrt : Real.sqrt x ≤ x / 6 := by
    have h6 : 6 ≤ Real.sqrt x := by
      rw [Real.le_sqrt (by norm_num) hx0.le]; linarith
    have := Real.mul_self_sqrt hx0.le
    nlinarith
  have hEx : E ≤ 10 * x / 3 := by
    rw [hE]; unfold shortEndpoint; rw [← hx]; nlinarith
  have hx2 : 2500 ≤ x ^ 2 := by nlinarith
  have hLE : E < L := by
    have : 10 * x / 3 < x ^ 3 := by nlinarith
    rw [hLx]; linarith
  -- short ≥ 0 and short ≤ (E/2) e^{(1+δ)E}
  have hsm : ∀ a ∈ Icc (shortCutoff ε) E, 0 ≤ -shortShellDensity ε a ∧
      -shortShellDensity ε a * a ^ 2 ≤ 1 / 2 := by
    intro a ha
    have ha0 : 0 < a := hc0.trans_le ha.1
    have hm := hmargin a ha
    have hm1 : shortMargin ε a ≤ 1 := by
      unfold shortMargin; have : 0 ≤ 10 * ε * (1 + a) := by positivity
      linarith
    have hcosh := Real.one_le_cosh a
    have hexp : Real.exp (-2 * a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    unfold shortShellDensity
    rw [neg_neg]
    constructor
    · positivity
    · rw [show shortMargin ε a * Real.exp (-2 * a) / (2 * a ^ 2 * Real.cosh a) * a ^ 2 =
        shortMargin ε a * Real.exp (-2 * a) / (2 * Real.cosh a) by field_simp]
      rw [div_le_iff₀ (by positivity)]
      have : shortMargin ε a * Real.exp (-2 * a) ≤ 1 := by
        calc shortMargin ε a * Real.exp (-2 * a) ≤ 1 * 1 :=
              mul_le_mul hm1 hexp (Real.exp_pos _).le zero_le_one
          _ = 1 := by ring
      nlinarith
  have hsint : IntervalIntegrable (fun a => -shortShellDensity ε a * a ^ 2 * Real.cosh ((1 + δ) * a))
      volume (shortCutoff ε) E := by
    have h0 := (shortShellDensity_intervalIntegrable hε0 horder).neg.mul_continuousOn
      (Continuous.continuousOn (f := fun a : ℝ => a ^ 2 * Real.cosh ((1 + δ) * a)) (by fun_prop))
    convert h0 using 1
    funext a; simp only [Pi.neg_apply]; ring
  have hshort0 : 0 ≤ upperShortShellVariance ε δ := by
    unfold upperShortShellVariance
    apply intervalIntegral.integral_nonneg horder
    intro a ha
    have := Real.cosh_pos ((1 + δ) * a)
    have h := hsm a ha
    have : 0 ≤ -shortShellDensity ε a * a ^ 2 := mul_nonneg h.1 (sq_nonneg a)
    positivity
  have hshort : upperShortShellVariance ε δ ≤ (E / 2) * Real.exp ((1 + δ) * E) := by
    unfold upperShortShellVariance
    have hb : ∀ a ∈ Icc (shortCutoff ε) E, -shortShellDensity ε a * a ^ 2 * Real.cosh ((1 + δ) * a) ≤
        1 / 2 * Real.exp ((1 + δ) * E) := by
      intro a ha
      have ha0 : 0 < a := hc0.trans_le ha.1
      have h := hsm a ha
      have hch : Real.cosh ((1 + δ) * a) ≤ Real.exp ((1 + δ) * E) := by
        have hy : 0 ≤ (1 + δ) * a := by positivity
        have hc1 : Real.cosh ((1 + δ) * a) ≤ Real.exp ((1 + δ) * a) := by
          rw [Real.cosh_eq]
          have : Real.exp (-((1 + δ) * a)) ≤ Real.exp ((1 + δ) * a) := Real.exp_le_exp.mpr (by linarith)
          linarith
        refine hc1.trans (Real.exp_le_exp.mpr ?_)
        exact mul_le_mul_of_nonneg_left ha.2 (by linarith)
      exact mul_le_mul h.2 hch (Real.cosh_pos _).le (by norm_num)
    have := intervalIntegral.integral_mono_on horder hsint intervalIntegrable_const hb
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have hlen : E - shortCutoff ε ≤ E := by linarith
    calc _ ≤ (E - shortCutoff ε) * (1 / 2 * Real.exp ((1 + δ) * E)) := this
      _ ≤ E * (1 / 2 * Real.exp ((1 + δ) * E)) :=
          mul_le_mul_of_nonneg_right hlen (by positivity)
      _ = _ := by ring
  -- pos ≥ (w L^2 / 2) e^{δ L}
  have hL0 : 0 < L := by linarith
  have hw0 : 0 < w := shellWeight_pos ε
  have hpos : w * L ^ 2 / 2 * Real.exp (δ * L) ≤ upperPositiveShellVariance ε δ := by
    unfold upperPositiveShellVariance
    have hconst : (∫ a in L..L + 1, w * L ^ 2 / 2 * Real.exp (δ * L)) = w * L ^ 2 / 2 * Real.exp (δ * L) := by
      simp
    rw [← hconst]
    apply intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
    · exact (Continuous.intervalIntegrable (by
        have := positiveShellDensity_continuous ε; fun_prop) _ _)
    · intro a ha
      have ha0 : 0 < a := hL0.trans_le ha.1
      unfold positiveShellDensity
      rw [← hw]
      have hca := Real.cosh_pos a
      have h1 : Real.exp ((1 + δ) * a) / 2 ≤ Real.cosh ((1 + δ) * a) := by
        rw [Real.cosh_eq]; have := Real.exp_pos (-((1 + δ) * a)); linarith
      have h2 : Real.cosh a ≤ Real.exp a := by
        rw [Real.cosh_eq]; have : Real.exp (-a) ≤ Real.exp a := Real.exp_le_exp.mpr (by linarith)
        linarith
      have h3 : Real.exp ((1 + δ) * a) = Real.exp a * Real.exp (δ * a) := by
        rw [← Real.exp_add]; ring_nf
      have h4 : Real.exp (δ * L) ≤ Real.exp (δ * a) := Real.exp_le_exp.mpr (by nlinarith [ha.1])
      have hL2 : L ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hL0.le ha.1 2
      have key : Real.exp (δ * a) / 2 ≤ Real.cosh ((1 + δ) * a) / Real.cosh a := by
        rw [le_div_iff₀ hca]
        calc Real.exp (δ * a) / 2 * Real.cosh a ≤ Real.exp (δ * a) / 2 * Real.exp a := by
              apply mul_le_mul_of_nonneg_left h2; positivity
          _ = Real.exp ((1 + δ) * a) / 2 := by rw [h3]; ring
          _ ≤ _ := h1
      calc w * L ^ 2 / 2 * Real.exp (δ * L) ≤ w * a ^ 2 * (Real.exp (δ * a) / 2) := by
            have := mul_le_mul hL2 h4 (Real.exp_pos _).le (sq_nonneg a)
            nlinarith
        _ ≤ w * a ^ 2 * (Real.cosh ((1 + δ) * a) / Real.cosh a) := by
            apply mul_le_mul_of_nonneg_left key; positivity
        _ = w / Real.cosh a * a ^ 2 * Real.cosh ((1 + δ) * a) := by field_simp
  -- comparison
  have hcmp : 100 * ((E / 2) * Real.exp ((1 + δ) * E)) ≤ w * L ^ 2 / 2 * Real.exp (δ * L) := by
    have h100 : 100 * E ≤ Real.exp x := by
      have := Real.pow_div_factorial_le_exp x hx0.le 3
      simp [Nat.factorial] at this
      have : 1000 * x / 3 ≤ x ^ 3 / 6 := by nlinarith
      linarith
    have hexpo : x + E ≤ -(3 * ε * L / 8) + ε / 2 * (L - E) := by
      have hεL : ε * L = x ^ 2 := by rw [hLx]; have := hεx; nlinarith
      have hεE : ε * E ≤ 10 / 3 := by
        have := mul_le_mul_of_nonneg_left hEx hε0.le
        have e : ε * (10 * x / 3) = 10 / 3 := by rw [mul_div_assoc', ← mul_assoc, mul_comm ε 10, mul_assoc, hεx]; ring
        linarith
      nlinarith
    have hwexp : w = Real.exp (-(3 * ε * L / 8)) := by
      rw [hw]; unfold shellWeight; congr 1; rw [hL]; ring
    have hL1 : 1 ≤ L ^ 2 := by
      have : 1 ≤ x ^ 3 := one_le_pow₀ (by linarith)
      rw [hLx]; nlinarith
    have hδLE : ε / 2 * (L - E) ≤ δ * (L - E) := mul_le_mul_of_nonneg_right hδ (by linarith)
    have step : 100 * E * Real.exp E ≤ Real.exp (-(3 * ε * L / 8) + δ * (L - E)) := by
      calc 100 * E * Real.exp E ≤ Real.exp x * Real.exp E :=
            mul_le_mul_of_nonneg_right h100 (Real.exp_pos _).le
        _ = Real.exp (x + E) := by rw [Real.exp_add]
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    have e1 : Real.exp ((1 + δ) * E) = Real.exp E * Real.exp (δ * E) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : w * Real.exp (δ * L) = Real.exp (-(3 * ε * L / 8) + δ * (L - E)) * Real.exp (δ * E) := by
      rw [hwexp, ← Real.exp_add, ← Real.exp_add]; ring_nf
    have hdE := Real.exp_pos (δ * E)
    calc 100 * ((E / 2) * Real.exp ((1 + δ) * E)) = (100 * E * Real.exp E) * Real.exp (δ * E) / 2 := by
          rw [e1]; ring
      _ ≤ Real.exp (-(3 * ε * L / 8) + δ * (L - E)) * Real.exp (δ * E) / 2 := by
          gcongr
      _ = w * Real.exp (δ * L) / 2 := by rw [e2]
      _ ≤ w * L ^ 2 / 2 * Real.exp (δ * L) := by
          have := mul_le_mul_of_nonneg_left hL1 (show 0 ≤ w * Real.exp (δ * L) by positivity)
          nlinarith
  unfold upperNetShellVariance
  constructor <;> nlinarith

theorem h48_pos_lb {ε δ : ℝ} (hε0 : 0 < ε) (hδ0 : 0 ≤ δ) :
    shellWeight ε * shellLocation ε ^ 2 / 2 ≤ upperPositiveShellVariance ε δ := by
  set L := shellLocation ε with hL
  set w := shellWeight ε with hw
  have hL0 : 0 < L := by rw [hL]; unfold shellLocation; positivity
  have hw0 : 0 < w := shellWeight_pos ε
  unfold upperPositiveShellVariance
  have hconst : (∫ a in L..L + 1, w * L ^ 2 / 2) = w * L ^ 2 / 2 := by simp
  rw [← hconst]
  apply intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
  · exact (Continuous.intervalIntegrable (by
      have := positiveShellDensity_continuous ε; fun_prop) _ _)
  · intro a ha
    have ha0 : 0 < a := hL0.trans_le ha.1
    unfold positiveShellDensity
    rw [← hw]
    have hca := Real.cosh_pos a
    have h1 : Real.cosh a ≤ Real.cosh ((1 + δ) * a) := by
      rw [Real.cosh_le_cosh, abs_mul, abs_of_pos ha0, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 + δ)]
      nlinarith
    have hL2 : L ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hL0.le ha.1 2
    have : 1 ≤ Real.cosh ((1 + δ) * a) / Real.cosh a := by rw [le_div_iff₀ hca]; linarith
    calc w * L ^ 2 / 2 ≤ w * a ^ 2 * 1 := by nlinarith
      _ ≤ w * a ^ 2 * (Real.cosh ((1 + δ) * a) / Real.cosh a) := by
          apply mul_le_mul_of_nonneg_left this; positivity
      _ = w / Real.cosh a * a ^ 2 * Real.cosh ((1 + δ) * a) := by field_simp

theorem solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ κ : ℝ, 0 < κ →
        ∀ᶠ ℓ : ℝ in atTop,
          ∀ δ : ℝ, ε / 2 ≤ δ →
            saddleSourceSecondBranchCentralRadius ε ℓ (1 + δ) < κ := by
  filter_upwards [self_mem_nhdsWithin, h48_net_ev] with ε hε hnet
  have hε0 : 0 < ε := hε
  intro κ hκ
  set c0 : ℝ := (99 / 100) * (shellWeight ε * shellLocation ε ^ 2 / 2) with hc0
  have hc0p : 0 < c0 := by
    have := shellWeight_pos ε
    have : 0 < shellLocation ε := by unfold shellLocation; positivity
    positivity
  -- eventually ℓ^{-5/12} / sqrt c0 < κ
  have ht : Tendsto (fun ℓ : ℝ => ℓ ^ (-(5 / 12 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hev := ht.eventually (gt_mem_nhds (show (0:ℝ) < κ * Real.sqrt c0 by positivity))
  filter_upwards [hev, Filter.eventually_gt_atTop (0 : ℝ)] with ℓ hℓk hℓ
  intro δ hδ
  have hδ0 : 0 ≤ δ := by linarith
  have hV : c0 ≤ saddleSourceGaussianVariance ε ℓ (1 + δ) := by
    unfold saddleSourceGaussianVariance upperSaddleVariance
    rw [show 1 + δ - 1 = δ by ring]
    have h1 := (hnet δ hδ).1
    have h2 := h48_pos_lb hε0 hδ0
    have h3 := h48_gvar_ge ℓ (2 + δ) hℓ (by linarith)
    have h4 : 0 < 1 / (2 * (2 + δ)) := by positivity
    rw [hc0]; nlinarith
  unfold saddleSourceSecondBranchCentralRadius
  have hs : Real.sqrt c0 * Real.sqrt ℓ ≤ Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ)) := by
    rw [← Real.sqrt_mul hc0p.le]
    apply Real.sqrt_le_sqrt; nlinarith
  have hsp : 0 < Real.sqrt c0 * Real.sqrt ℓ := by
    have := Real.sqrt_pos.mpr hc0p; have := Real.sqrt_pos.mpr hℓ; positivity
  calc ℓ ^ (1 / 12 : ℝ) / Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ))
      ≤ ℓ ^ (1 / 12 : ℝ) / (Real.sqrt c0 * Real.sqrt ℓ) :=
        div_le_div_of_nonneg_left (by positivity) hsp hs
    _ = ℓ ^ (-(5 / 12 : ℝ)) / Real.sqrt c0 := by
        rw [Real.sqrt_eq_rpow ℓ]
        have : ℓ ^ (-(5 / 12 : ℝ)) = ℓ ^ (1 / 12 : ℝ) / ℓ ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_sub hℓ]; norm_num
        rw [this]; field_simp
    _ < κ := by
        rw [div_lt_iff₀ (Real.sqrt_pos.mpr hc0p)]; exact hℓk

