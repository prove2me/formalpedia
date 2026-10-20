-- Prove2me | solution 2 for CohnElkies.eventually_saddleSourceFirstBranch_central_radius_lt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:32:14.465822+00:00
-- url     : https://prove2.me/submissions/8a5d0b2a-b14b-4ede-bdf2-168b712c8db3

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

theorem h48_var_lb {ε ℓ u : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hℓ : 0 < ℓ)
    (hulower : -1 < u) (huupper : u ≤ 1 + ε / 2)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε), 0 ≤ shortMargin ε a) :
    2 * ε / (1 + u) ≤ saddleSourceGaussianVariance ε ℓ u := by
  have hη : 0 < 1 + u := by linarith
  have hsv := h48_short_var_le hε hεsmall hℓ hulower huupper horder hmargin
  have hgv := h48_gvar_ge ℓ (1 + u) hℓ hη
  have hpd : ∀ a, 0 ≤ positiveShellDensity ε a := fun a => by
    unfold positiveShellDensity; have := shellWeight_pos ε; have := Real.cosh_pos a; positivity
  have hposnn : 0 ≤ upperPositiveShellVariance ε (u - 1) := by
    unfold upperPositiveShellVariance
    apply intervalIntegral.integral_nonneg (by linarith)
    intro a _
    have := Real.cosh_pos ((1 + (u - 1)) * a)
    exact mul_nonneg (mul_nonneg (hpd a) (sq_nonneg a)) this.le
  unfold saddleSourceGaussianVariance upperSaddleVariance upperNetShellVariance
  rw [show 2 + (u - 1) = 1 + u by ring]
  have : 1 / (2 * (1 + u)) * (4 * ε) = 2 * ε / (1 + u) := by field_simp; ring
  nlinarith

theorem solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ κ : ℝ, 0 < κ →
        ∀ᶠ ℓ : ℝ in atTop,
          ∀ u : ℝ, -1 < u → u ≤ 1 + ε / 2 →
            Real.log ℓ / 4 ≤ ℓ * (1 + u) →
              saddleSourceFirstBranchCentralRadius ε ℓ u < κ := by
  filter_upwards [self_mem_nhdsWithin, h48_margin_ev, eventually_upper_shortCutoff_le_shortEndpoint,
    Ioo_mem_nhdsGT (show (0:ℝ) < 1 / 4 by norm_num)]
    with ε hε hmargin horder hε4
  have hε0 : 0 < ε := hε
  have hεsmall : ε ≤ 1 / 4 := hε4.2.le
  intro κ hκ
  set A : ℝ := (2 + ε / 2) / Real.sqrt (2 * ε) with hA
  have hc : 0 < Real.sqrt (2 * ε) := Real.sqrt_pos.mpr (by positivity)
  have hA0 : 0 < A := by positivity
  -- choose M with A * M^(-5/12) < κ
  set M : ℝ := ((A / κ) ^ (12 / 5 : ℝ)) + 1 with hM
  have hM0 : 0 < M := by positivity
  have hMk : A * M ^ (-(5 / 12 : ℝ)) < κ := by
    have h1 : (A / κ) ^ (12 / 5 : ℝ) < M := by linarith
    have h2 : A / κ < M ^ (5 / 12 : ℝ) := by
      have := Real.rpow_lt_rpow (by positivity) h1 (show (0:ℝ) < 5 / 12 by norm_num)
      rwa [← Real.rpow_mul (by positivity), show (12 / 5 : ℝ) * (5 / 12) = 1 by norm_num,
        Real.rpow_one] at this
    rw [Real.rpow_neg hM0.le, ← div_eq_mul_inv, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hκ] at h2; linarith
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ),
    (Real.tendsto_log_atTop.eventually_ge_atTop (4 * M))] with ℓ hℓ1 hlog
  intro u hu1 hu2 hX
  have hℓ : 0 < ℓ := by linarith
  have hη : 0 < 1 + u := by linarith
  set X : ℝ := ℓ * (1 + u) with hXd
  have hXM : M ≤ X := by linarith
  have hX0 : 0 < X := by positivity
  have hV := h48_var_lb (ℓ := ℓ) hε0 hεsmall hℓ hu1 hu2 horder hmargin
  unfold saddleSourceFirstBranchCentralRadius
  rw [← hXd]
  have hs : Real.sqrt (2 * ε) * Real.sqrt X / (1 + u) ≤
      Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show Real.sqrt (2 * ε * X) / (1 + u) = Real.sqrt (2 * ε * X / (1 + u) ^ 2) by
      rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hη.le]]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hV (show 0 ≤ ℓ * (1 + u) ^ 2 by positivity)
    have e : ℓ * (1 + u) ^ 2 * (2 * ε / (1 + u)) = 2 * ε * X := by rw [hXd]; field_simp
    nlinarith
  have hsp : 0 < Real.sqrt (2 * ε) * Real.sqrt X / (1 + u) := by
    have := Real.sqrt_pos.mpr hX0; positivity
  calc X ^ (1 / 12 : ℝ) / Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u)
      ≤ X ^ (1 / 12 : ℝ) / (Real.sqrt (2 * ε) * Real.sqrt X / (1 + u)) :=
        div_le_div_of_nonneg_left (by positivity) hsp hs
    _ = (1 + u) / Real.sqrt (2 * ε) * X ^ (-(5 / 12 : ℝ)) := by
        rw [Real.sqrt_eq_rpow]
        have : X ^ (-(5 / 12 : ℝ)) = X ^ (1 / 12 : ℝ) / X ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_sub hX0]; norm_num
        rw [this]; field_simp
        try exact (Real.sqrt_eq_rpow X).symm
    _ ≤ A * M ^ (-(5 / 12 : ℝ)) := by
        rw [hA]
        apply mul_le_mul
        · apply div_le_div_of_nonneg_right (by linarith) hc.le
        · exact Real.rpow_le_rpow_of_nonpos hM0 hXM (by norm_num)
        · positivity
        · positivity
    _ < κ := hMk

