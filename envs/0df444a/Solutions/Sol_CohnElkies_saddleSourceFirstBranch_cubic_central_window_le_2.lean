-- Prove2me | solution 2 for CohnElkies.saddleSourceFirstBranch_cubic_central_window_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:24:46.222983+00:00
-- url     : https://prove2.me/submissions/e732dec0-5f4f-4b6e-b8a3-903054195a0c

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

theorem h48_majorant_integral (ℓ η : ℝ) (hη : 0 < η) :
    (∫ a in Set.Ioi (0:ℝ), (ℓ / 2 + a) * Real.exp (-η * a)) = ℓ / (2 * η) + 1 / η ^ 2 := by
  have h0 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (0 : ℝ)) (p := 1) (b := η)
    (by norm_num) one_pos hη
  have h1 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (1 : ℝ)) (p := 1) (b := η)
    (by norm_num) one_pos hη
  simp only [Real.rpow_zero, Real.rpow_one, one_mul] at h0 h1
  have e : (fun a : ℝ => (ℓ / 2 + a) * Real.exp (-η * a)) =
      fun a => ℓ / 2 * Real.exp (-η * a) + a * Real.exp (-η * a) := by
    funext a; ring
  rw [e, MeasureTheory.integral_add (h0.const_mul _) h1, MeasureTheory.integral_const_mul,
    integral_exp_mul_Ioi (by linarith) 0]
  have hG := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := η) two_pos hη
  have hc : (∫ t : ℝ in Set.Ioi 0, t ^ ((2:ℝ) - 1) * Real.exp (-(η * t))) =
      ∫ t : ℝ in Set.Ioi 0, t * Real.exp (-η * t) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only
    norm_num
  rw [hc, Real.Gamma_two] at hG
  rw [hG]
  simp
  field_simp

theorem h48_short_var_le {ε ℓ u : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε),
      0 ≤ shortMargin ε a) :
    upperShortShellVariance ε (u - 1) ≤
      (1 - 4 * ε) * upperGammaVariance ℓ (1 + u) := by
  have hη : 0 < 1 + u := by linarith
  have hc0 : 0 < shortCutoff ε := by unfold shortCutoff; positivity
  have h14 : 0 ≤ 1 - 4 * ε := by linarith
  have hs := shortShellDensity_intervalIntegrable hε horder
  unfold upperShortShellVariance upperGammaVariance
  have hpt : ∀ a ∈ Set.Icc (shortCutoff ε) (shortEndpoint ε),
      (-shortShellDensity ε a) * a ^ 2 * Real.cosh ((1 + (u - 1)) * a) ≤
        ((1 - 4 * ε) * ℓ⁻¹) * (a ^ 2 * upperGammaMeasureDensity ℓ (1 + u) a) := by
    intro a ha
    have ha0 : 0 < a := hc0.trans_le ha.1
    have h := h48_pw hε hεsmall hℓ ha0 hulower.le huupper (hmargin a ha)
    rw [show (1 + (u - 1)) * a = u * a by ring]
    have h2 := mul_le_mul_of_nonneg_right h (show 0 ≤ a ^ 2 * ℓ⁻¹ by positivity)
    have e1 : ℓ * -shortShellDensity ε a * Real.cosh (u * a) * (a ^ 2 * ℓ⁻¹) =
        -shortShellDensity ε a * a ^ 2 * Real.cosh (u * a) := by
      field_simp
    have e2 : (1 - 4 * ε) * upperGammaMeasureDensity ℓ (1 + u) a * (a ^ 2 * ℓ⁻¹) =
        ((1 - 4 * ε) * ℓ⁻¹) * (a ^ 2 * upperGammaMeasureDensity ℓ (1 + u) a) := by ring
    linarith
  have hint := h48_int_var ℓ (1 + u) hℓ hη
  calc (∫ a in shortCutoff ε..shortEndpoint ε,
        (-shortShellDensity ε a) * a ^ 2 * Real.cosh ((1 + (u - 1)) * a))
      ≤ ∫ a in shortCutoff ε..shortEndpoint ε,
          ((1 - 4 * ε) * ℓ⁻¹) * (a ^ 2 * upperGammaMeasureDensity ℓ (1 + u) a) := by
        apply intervalIntegral.integral_mono_on horder
        · have h0 := hs.neg.mul_continuousOn (Continuous.continuousOn
            (f := fun a : ℝ => a ^ 2 * Real.cosh ((1 + (u - 1)) * a)) (by fun_prop))
          convert h0 using 1
          funext a; simp only [Pi.neg_apply]; ring
        · apply IntervalIntegrable.const_mul
          rw [intervalIntegrable_iff_integrableOn_Icc_of_le horder]
          exact hint.mono_set (fun a ha => hc0.trans_le ha.1)
        · exact hpt
    _ = ((1 - 4 * ε) * ℓ⁻¹) * ∫ a in Set.Ioc (shortCutoff ε) (shortEndpoint ε),
          a ^ 2 * upperGammaMeasureDensity ℓ (1 + u) a := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le horder]
    _ ≤ ((1 - 4 * ε) * ℓ⁻¹) * ∫ a in Set.Ioi 0, a ^ 2 * upperGammaMeasureDensity ℓ (1 + u) a := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply MeasureTheory.setIntegral_mono_set hint
        · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun a ha => ?_))
          have ha' : (0:ℝ) < a := ha
          exact mul_nonneg (sq_nonneg _) (h48_dens_nonneg ℓ (1 + u) hℓ ha')
        · exact Filter.Eventually.of_forall (fun a ha => hc0.trans_le (le_of_lt ha.1))
    _ = (1 - 4 * ε) * (ℓ⁻¹ * ∫ a in Set.Ioi 0, a ^ 2 * upperGammaMeasureDensity ℓ (1 + u) a) := by ring

theorem h48_gvar_le (ℓ η : ℝ) (hℓ : 0 < ℓ) (hη : 0 < η) (hscale : 1 ≤ ℓ * η) :
    upperGammaVariance ℓ η ≤ (3 / 2) / η := by
  unfold upperGammaVariance
  have hle : (∫ a in Set.Ioi (0:ℝ), a ^ 2 * upperGammaMeasureDensity ℓ η a) ≤
      ∫ a in Set.Ioi (0:ℝ), (ℓ / 2 + a) * Real.exp (-η * a) := by
    apply MeasureTheory.setIntegral_mono_on (h48_int_var ℓ η hℓ hη)
      (h48_majorant_int ℓ η hη) measurableSet_Ioi
    intro a ha
    exact h48_sq_dens_le ℓ η hℓ ha
  rw [h48_majorant_integral ℓ η hη] at hle
  have hl : 0 < ℓ⁻¹ := inv_pos.mpr hℓ
  have h1 : 1 / (ℓ * η) ≤ 1 := by rw [div_le_one (by positivity)]; exact hscale
  calc ℓ⁻¹ * (∫ a in Set.Ioi (0:ℝ), a ^ 2 * upperGammaMeasureDensity ℓ η a)
      ≤ ℓ⁻¹ * (ℓ / (2 * η) + 1 / η ^ 2) := mul_le_mul_of_nonneg_left hle hl.le
    _ = 1 / (2 * η) + 1 / (ℓ * η) / η := by field_simp
    _ ≤ 1 / (2 * η) + 1 / η := by gcongr <;> linarith
    _ = (3 / 2) / η := by field_simp; ring

theorem h48_g3_le (ℓ η T : ℝ) (hℓ : 0 < ℓ) (hη : 0 < η) (hscale : 1 ≤ ℓ * η) :
    upperGammaThirdMoment ℓ η ≤ (5 / 2) / η ^ 2 := by
  have h1 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (1 : ℝ)) (p := 1) (b := η)
    (by norm_num) one_pos hη
  have h2 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (2 : ℝ)) (p := 1) (b := η)
    (by norm_num) one_pos hη
  simp only [Real.rpow_one] at h1 h2
  have h2' : IntegrableOn (fun a : ℝ => a ^ 2 * Real.exp (-η * a)) (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun h2 (fun a ha => ?_) measurableSet_Ioi
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hM : IntegrableOn (fun a : ℝ => a * ((ℓ / 2 + a) * Real.exp (-η * a))) (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun ((h1.const_mul (ℓ / 2)).add h2') (fun a ha => ?_) measurableSet_Ioi
    simp only [Pi.add_apply]; ring
  have hI3 : IntegrableOn (fun a : ℝ => a ^ 3 * upperGammaMeasureDensity ℓ η a) (Set.Ioi 0) := by
    refine hM.mono' ?_ ?_
    · exact ((continuousOn_id.pow 3).mul (h48_dens_contOn ℓ η hℓ)).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun a ha => ?_))
      have ha' : (0:ℝ) < a := ha
      have hd := h48_dens_nonneg ℓ η hℓ ha'
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have := mul_le_mul_of_nonneg_left (h48_sq_dens_le ℓ η hℓ ha') ha'.le
      calc a ^ 3 * upperGammaMeasureDensity ℓ η a = a * (a ^ 2 * upperGammaMeasureDensity ℓ η a) := by ring
        _ ≤ _ := this
  have hle : (∫ a in Set.Ioi (0:ℝ), a ^ 3 * upperGammaMeasureDensity ℓ η a) ≤
      ∫ a in Set.Ioi (0:ℝ), a * ((ℓ / 2 + a) * Real.exp (-η * a)) := by
    apply MeasureTheory.setIntegral_mono_on hI3 hM measurableSet_Ioi
    intro a ha
    have ha' : (0:ℝ) < a := ha
    have := mul_le_mul_of_nonneg_left (h48_sq_dens_le ℓ η hℓ ha') ha'.le
    calc a ^ 3 * upperGammaMeasureDensity ℓ η a = a * (a ^ 2 * upperGammaMeasureDensity ℓ η a) := by ring
      _ ≤ _ := this
  have hval : (∫ a in Set.Ioi (0:ℝ), a * ((ℓ / 2 + a) * Real.exp (-η * a))) =
      ℓ / (2 * η ^ 2) + 2 / η ^ 3 := by
    have e : (fun a : ℝ => a * ((ℓ / 2 + a) * Real.exp (-η * a))) =
        fun a => ℓ / 2 * (a * Real.exp (-η * a)) + a ^ 2 * Real.exp (-η * a) := by
      funext a; ring
    rw [e, MeasureTheory.integral_add (h1.const_mul _) h2', MeasureTheory.integral_const_mul]
    have hA := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := η) two_pos hη
    have hB := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 3) (r := η) (by norm_num) hη
    have cA : (∫ t : ℝ in Set.Ioi 0, t ^ ((2:ℝ) - 1) * Real.exp (-(η * t))) =
        ∫ t : ℝ in Set.Ioi 0, t * Real.exp (-η * t) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t _; simp only; norm_num
    have cB : (∫ t : ℝ in Set.Ioi 0, t ^ ((3:ℝ) - 1) * Real.exp (-(η * t))) =
        ∫ t : ℝ in Set.Ioi 0, t ^ 2 * Real.exp (-η * t) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t _; simp only; norm_num
    have g3 : Real.Gamma 3 = 2 := by
      rw [show (3:ℝ) = 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), Real.Gamma_two]; norm_num
    rw [cA, Real.Gamma_two] at hA
    rw [cB, g3] at hB
    rw [hA, hB]
    have e2 : (1 / η) ^ (2:ℝ) = 1 / η ^ 2 := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; ring
    have e3 : (1 / η) ^ (3:ℝ) = 1 / η ^ 3 := by
      rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]; ring
    rw [e2, e3]; field_simp
  unfold upperGammaThirdMoment
  rw [hval] at hle
  have hl : 0 < ℓ⁻¹ := inv_pos.mpr hℓ
  have h1' : 1 / (ℓ * η) ≤ 1 := by rw [div_le_one (by positivity)]; exact hscale
  calc ℓ⁻¹ * (∫ a in Set.Ioi (0:ℝ), a ^ 3 * upperGammaMeasureDensity ℓ η a)
      ≤ ℓ⁻¹ * (ℓ / (2 * η ^ 2) + 2 / η ^ 3) := mul_le_mul_of_nonneg_left hle hl.le
    _ = 1 / (2 * η ^ 2) + 2 * (1 / (ℓ * η)) / η ^ 2 := by field_simp
    _ ≤ 1 / (2 * η ^ 2) + 2 * 1 / η ^ 2 := by gcongr
    _ = (5 / 2) / η ^ 2 := by field_simp; ring

theorem h48_third {ε ℓ u : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε)
      (shortEndpoint ε), 0 ≤ shortMargin ε a)
    (hscale : 1 ≤ ℓ * (1 + u)) :
    (1 + u) ^ 2 * upperSaddleThirdMoment ε ℓ (u - 1) ≤
      saddleSourceFirstBranchThirdMomentCoefficient ε := by
  have hη : 0 < 1 + u := by linarith
  have hc0 : 0 < shortCutoff ε := by unfold shortCutoff; positivity
  have hE0 : 0 < shortEndpoint ε := hc0.trans_le horder
  have hs := shortShellDensity_intervalIntegrable hε horder
  unfold saddleSourceFirstBranchThirdMomentCoefficient upperSaddleThirdMoment upperNetShellThirdMoment
  rw [show 2 + (u - 1) = 1 + u by ring]
  have hg3 := h48_g3_le ℓ (1 + u) 0 hℓ hη hscale
  have hg3' : (1 + u) ^ 2 * upperGammaThirdMoment ℓ (1 + u) ≤ 5 / 2 := by
    have := mul_le_mul_of_nonneg_left hg3 (sq_nonneg (1 + u))
    rwa [mul_div_assoc', mul_div_cancel_left₀ _ (by positivity)] at this
  -- short third moment
  have hsnn : ∀ a ∈ Set.Icc (shortCutoff ε) (shortEndpoint ε), ∀ k : ℕ,
      0 ≤ (-shortShellDensity ε a) * a ^ k * Real.cosh ((1 + (u - 1)) * a) := by
    intro a ha k
    have ha0 : 0 < a := hc0.trans_le ha.1
    have hm := hmargin a ha
    have h1 : 0 ≤ -shortShellDensity ε a := by
      unfold shortShellDensity; rw [neg_neg]; have := Real.cosh_pos a; positivity
    have := Real.cosh_pos ((1 + (u - 1)) * a)
    positivity
  have hs3 : upperShortShellThirdMoment ε (u - 1) ≤ shortEndpoint ε * upperShortShellVariance ε (u - 1) := by
    unfold upperShortShellThirdMoment upperShortShellVariance
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on horder
    · have h0 := hs.neg.mul_continuousOn (Continuous.continuousOn
        (f := fun a : ℝ => a ^ 3 * Real.cosh ((1 + (u - 1)) * a)) (by fun_prop))
      convert h0 using 1
      funext a; simp only [Pi.neg_apply]; ring
    · have h0 := (hs.neg.mul_continuousOn (Continuous.continuousOn
        (f := fun a : ℝ => a ^ 2 * Real.cosh ((1 + (u - 1)) * a)) (by fun_prop))).const_mul (shortEndpoint ε)
      convert h0 using 1
      funext a; simp only [Pi.neg_apply]; ring
    · intro a ha
      have h2 := hsnn a ha 2
      have : (-shortShellDensity ε a) * a ^ 3 * Real.cosh ((1 + (u - 1)) * a) =
          a * ((-shortShellDensity ε a) * a ^ 2 * Real.cosh ((1 + (u - 1)) * a)) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right ha.2 h2
  have hsv := h48_short_var_le hε hεsmall hℓ hulower huupper horder hmargin
  have hgv := h48_gvar_le ℓ (1 + u) hℓ hη hscale
  have hsvnn : 0 ≤ upperShortShellVariance ε (u - 1) := by
    unfold upperShortShellVariance
    exact intervalIntegral.integral_nonneg horder (fun a ha => hsnn a ha 2)
  have hgvnn : 0 ≤ upperGammaVariance ℓ (1 + u) := by
    unfold upperGammaVariance
    exact mul_nonneg (inv_nonneg.mpr hℓ.le) (MeasureTheory.setIntegral_nonneg measurableSet_Ioi
      (fun a ha => mul_nonneg (sq_nonneg a) (h48_dens_nonneg ℓ _ hℓ ha)))
  have hshort' : (1 + u) ^ 2 * upperShortShellThirdMoment ε (u - 1) ≤
      (3 / 2) * shortEndpoint ε * (2 + ε / 2) := by
    have h1 : upperShortShellVariance ε (u - 1) ≤ (3 / 2) / (1 + u) := by
      have : (1 - 4 * ε) * upperGammaVariance ℓ (1 + u) ≤ upperGammaVariance ℓ (1 + u) := by
        nlinarith
      linarith
    have h2 : (1 + u) * upperShortShellVariance ε (u - 1) ≤ 3 / 2 := by
      rw [le_div_iff₀ hη] at h1; linarith
    calc (1 + u) ^ 2 * upperShortShellThirdMoment ε (u - 1)
        ≤ (1 + u) ^ 2 * (shortEndpoint ε * upperShortShellVariance ε (u - 1)) :=
          mul_le_mul_of_nonneg_left hs3 (sq_nonneg _)
      _ = shortEndpoint ε * (1 + u) * ((1 + u) * upperShortShellVariance ε (u - 1)) := by ring
      _ ≤ shortEndpoint ε * (1 + u) * (3 / 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ shortEndpoint ε * (2 + ε / 2) * (3 / 2) := by
          apply mul_le_mul_of_nonneg_right _ (by norm_num)
          exact mul_le_mul_of_nonneg_left (by linarith) hE0.le
      _ = _ := by ring
  -- positive part
  have hpd : ∀ a, 0 ≤ positiveShellDensity ε a := fun a => by
    unfold positiveShellDensity; have := shellWeight_pos ε; have := Real.cosh_pos a; positivity
  have hposmono : upperPositiveShellThirdMoment ε (u - 1) ≤ upperPositiveShellThirdMoment ε (ε / 2) := by
    unfold upperPositiveShellThirdMoment
    have hL : 0 < shellLocation ε := by unfold shellLocation; positivity
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (Continuous.intervalIntegrable (by
        have := positiveShellDensity_continuous ε; fun_prop) _ _)
    · exact (Continuous.intervalIntegrable (by
        have := positiveShellDensity_continuous ε; fun_prop) _ _)
    · intro a ha
      have ha0 : 0 ≤ a := le_trans hL.le ha.1
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hpd a) (pow_nonneg ha0 3))
      rw [Real.cosh_le_cosh, abs_mul, abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg a)
      rw [abs_le]; constructor
      · rw [abs_of_pos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
  have hposnn : 0 ≤ upperPositiveShellThirdMoment ε (ε / 2) := by
    unfold upperPositiveShellThirdMoment
    have hL : 0 < shellLocation ε := by unfold shellLocation; positivity
    apply intervalIntegral.integral_nonneg (by linarith)
    intro a ha
    have ha0 : 0 ≤ a := le_trans hL.le ha.1
    have := Real.cosh_pos ((1 + ε / 2) * a)
    exact mul_nonneg (mul_nonneg (hpd a) (pow_nonneg ha0 3)) this.le
  have hpos' : (1 + u) ^ 2 * upperPositiveShellThirdMoment ε (u - 1) ≤
      (2 + ε / 2) ^ 2 * upperPositiveShellThirdMoment ε (ε / 2) := by
    have hsq : (1 + u) ^ 2 ≤ (2 + ε / 2) ^ 2 := pow_le_pow_left₀ hη.le (by linarith) 2
    calc (1 + u) ^ 2 * upperPositiveShellThirdMoment ε (u - 1)
        ≤ (1 + u) ^ 2 * upperPositiveShellThirdMoment ε (ε / 2) :=
          mul_le_mul_of_nonneg_left hposmono (sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right hsq hposnn
  nlinarith [hg3', hshort', hpos']

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

theorem solution
    {ε ℓ u T : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε)
      (shortEndpoint ε), 0 ≤ shortMargin ε a)
    (hscale : 1 ≤ ℓ * (1 + u))
    (hT : |T| ≤ saddleSourceFirstBranchCentralRadius ε ℓ u) :
    (ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
        |T| ^ 3 ≤
      (saddleSourceFirstBranchThirdMomentCoefficient ε /
        (12 * ε * Real.sqrt (2 * ε))) *
          (ℓ * (1 + u)) ^ (-(1 / 4 : ℝ)) := by
  have hη : 0 < 1 + u := by linarith
  set η : ℝ := 1 + u with hηdef
  set X : ℝ := ℓ * η with hX
  have hX1 : 1 ≤ X := hscale
  have hX0 : 0 < X := by linarith
  set K := saddleSourceFirstBranchThirdMomentCoefficient ε with hK
  set Y : ℝ := X ^ (1 / 12 : ℝ) with hY
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hX0 _
  have hYpow : ∀ n : ℕ, Y ^ n = X ^ ((n : ℝ) / 12) := by
    intro n
    rw [hY, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; congr 1; ring
  have hX12 : X = Y ^ 12 := by rw [hYpow]; norm_num
  have hsqX : Real.sqrt X = Y ^ 6 := by
    rw [Real.sqrt_eq_rpow, hYpow]; norm_num
  have hXneg : X ^ (-(1 / 4 : ℝ)) = (Y ^ 3)⁻¹ := by
    rw [Real.rpow_neg hX0.le, hYpow]; norm_num
  -- variance lower bound
  have hsv := h48_short_var_le hε hεsmall hℓ hulower huupper horder hmargin
  have hgv := h48_gvar_ge ℓ η hℓ hη
  have hpd : ∀ a, 0 ≤ positiveShellDensity ε a := fun a => by
    unfold positiveShellDensity; have := shellWeight_pos ε; have := Real.cosh_pos a; positivity
  have hposnn : 0 ≤ upperPositiveShellVariance ε (u - 1) := by
    unfold upperPositiveShellVariance
    apply intervalIntegral.integral_nonneg (by linarith)
    intro a _
    have := Real.cosh_pos ((1 + (u - 1)) * a)
    exact mul_nonneg (mul_nonneg (hpd a) (sq_nonneg a)) this.le
  have hV : 2 * ε / η ≤ saddleSourceGaussianVariance ε ℓ u := by
    unfold saddleSourceGaussianVariance upperSaddleVariance upperNetShellVariance
    rw [show 2 + (u - 1) = η by rw [hηdef]; ring]
    have : 1 / (2 * η) * (4 * ε) = 2 * ε / η := by field_simp; ring
    nlinarith
  have hc : 0 < Real.sqrt (2 * ε) := Real.sqrt_pos.mpr (by positivity)
  have hc2 : Real.sqrt (2 * ε) ^ 2 = 2 * ε := Real.sq_sqrt (by positivity)
  -- s lower bound
  have hs : Real.sqrt (2 * ε) * Y ^ 6 / η ≤ Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) := by
    rw [Real.le_sqrt (by positivity) (mul_nonneg hℓ.le (le_trans (by positivity) hV))]
    rw [div_pow, mul_pow, hc2, ← pow_mul, show 6 * 2 = 12 by norm_num, ← hX12, div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hV (show 0 ≤ ℓ * η ^ 2 by positivity)
    have e : ℓ * η ^ 2 * (2 * ε / η) = 2 * ε * X := by rw [hX]; field_simp
    nlinarith
  have hspos : 0 < Real.sqrt (2 * ε) * Y ^ 6 / η := by positivity
  have hT' : |T| ≤ Y / (Real.sqrt (2 * ε) * Y ^ 6 / η) := by
    refine hT.trans ?_
    unfold saddleSourceFirstBranchCentralRadius
    rw [← hηdef, ← hX, ← hY]
    exact div_le_div_of_nonneg_left hY0.le hspos hs
  have hT3 : |T| ^ 3 ≤ (Y / (Real.sqrt (2 * ε) * Y ^ 6 / η)) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) hT' 3
  -- third moment bound
  have h3 := h48_third hε hεsmall hℓ hulower huupper horder hmargin hscale
  rw [← hηdef, ← hK] at h3
  have h3' : upperSaddleThirdMoment ε ℓ (u - 1) ≤ K / η ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hKnn : 0 ≤ K := by
    rw [hK]; unfold saddleSourceFirstBranchThirdMomentCoefficient
    have hE0 : 0 < shortEndpoint ε := (by unfold shortCutoff; positivity : 0 < shortCutoff ε).trans_le horder
    have : 0 ≤ upperPositiveShellThirdMoment ε (ε / 2) := by
      unfold upperPositiveShellThirdMoment
      have hL : 0 < shellLocation ε := by unfold shellLocation; positivity
      apply intervalIntegral.integral_nonneg (by linarith)
      intro a ha
      have ha0 : 0 ≤ a := le_trans hL.le ha.1
      have := Real.cosh_pos ((1 + ε / 2) * a)
      exact mul_nonneg (mul_nonneg (hpd a) (pow_nonneg ha0 3)) this.le
    positivity
  rw [hXneg]
  calc ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6 * |T| ^ 3
      ≤ ℓ * (K / η ^ 2) / 6 * |T| ^ 3 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact mul_le_mul_of_nonneg_left h3' hℓ.le
    _ ≤ ℓ * (K / η ^ 2) / 6 * (Y / (Real.sqrt (2 * ε) * Y ^ 6 / η)) ^ 3 := by
        apply mul_le_mul_of_nonneg_left hT3 (by positivity)
    _ = K / (12 * ε * Real.sqrt (2 * ε)) * (Y ^ 3)⁻¹ := by
        have hℓX : ℓ = Y ^ 12 / η := by rw [← hX12, hX]; field_simp
        rw [hℓX]
        generalize Real.sqrt (2 * ε) = c at hc hc2 ⊢
        have hε2 : ε = c ^ 2 / 2 := by linarith
        rw [hε2]
        field_simp
        ring

