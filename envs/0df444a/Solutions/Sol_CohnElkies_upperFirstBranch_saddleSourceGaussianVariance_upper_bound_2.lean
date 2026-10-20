-- Prove2me | solution 2 for CohnElkies.upperFirstBranch_saddleSourceGaussianVariance_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:18:51.400264+00:00
-- url     : https://prove2.me/submissions/6e4afc61-7548-4930-9fcb-cde3ae64d81b

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
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

theorem solution
    {ε ℓ u : ℝ}
    (hε : 0 < ε)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε)
      (shortEndpoint ε), 0 ≤ shortMargin ε a)
    (hscale : 1 ≤ ℓ * (1 + u)) :
    saddleSourceGaussianVariance ε ℓ u ≤
      ((3 / 2 : ℝ) +
          (2 + ε / 2) *
            upperPositiveShellVariance ε (ε / 2)) /
        (1 + u) := by
  have hη : 0 < 1 + u := by linarith
  have hc0 : 0 < shortCutoff ε := by unfold shortCutoff; positivity
  unfold saddleSourceGaussianVariance upperSaddleVariance upperNetShellVariance
  rw [show 2 + (u - 1) = 1 + u by ring]
  -- gamma part
  have hgam : upperGammaVariance ℓ (1 + u) ≤ (3 / 2) / (1 + u) := by
    unfold upperGammaVariance
    have hle : (∫ a in Set.Ioi (0:ℝ), a ^ 2 * upperGammaMeasureDensity ℓ (1 + u) a) ≤
        ∫ a in Set.Ioi (0:ℝ), (ℓ / 2 + a) * Real.exp (-(1 + u) * a) := by
      apply MeasureTheory.setIntegral_mono_on (h48_int_var ℓ (1 + u) hℓ hη)
        (h48_majorant_int ℓ (1 + u) hη) measurableSet_Ioi
      intro a ha
      exact h48_sq_dens_le ℓ (1 + u) hℓ ha
    rw [h48_majorant_integral ℓ (1 + u) hη] at hle
    have hl : 0 < ℓ⁻¹ := inv_pos.mpr hℓ
    calc ℓ⁻¹ * (∫ a in Set.Ioi (0:ℝ), a ^ 2 * upperGammaMeasureDensity ℓ (1 + u) a)
        ≤ ℓ⁻¹ * (ℓ / (2 * (1 + u)) + 1 / (1 + u) ^ 2) := mul_le_mul_of_nonneg_left hle hl.le
      _ = 1 / (2 * (1 + u)) + 1 / (ℓ * (1 + u)) / (1 + u) := by field_simp
      _ ≤ 1 / (2 * (1 + u)) + 1 / (1 + u) := by
        gcongr
        rw [div_le_one (by positivity)]
        exact (div_le_one (by positivity)).mpr hscale |>.trans (le_refl _) |> fun h => by
          rw [div_le_one (by positivity)] at h; linarith
      _ = (3 / 2) / (1 + u) := by field_simp; ring
  -- short part nonneg
  have hshort : 0 ≤ upperShortShellVariance ε (u - 1) := by
    unfold upperShortShellVariance
    apply intervalIntegral.integral_nonneg horder
    intro a ha
    have ha0 : 0 < a := hc0.trans_le ha.1
    have hm := hmargin a ha
    unfold shortShellDensity
    unfold shortMargin at hm
    have : 0 ≤ shortMargin ε a * Real.exp (-2 * a) / (2 * a ^ 2 * Real.cosh a) := by
      unfold shortMargin; have := Real.cosh_pos a; positivity
    have := Real.cosh_pos ((1 + (u - 1)) * a)
    nlinarith [sq_nonneg a, mul_nonneg (mul_nonneg ‹0 ≤ shortMargin ε a * Real.exp (-2 * a) / (2 * a ^ 2 * Real.cosh a)› (sq_nonneg a)) this.le]
  -- positive part
  have hpd : ∀ a, 0 ≤ positiveShellDensity ε a := fun a => by
    unfold positiveShellDensity; have := shellWeight_pos ε; have := Real.cosh_pos a; positivity
  have hposmono : upperPositiveShellVariance ε (u - 1) ≤ upperPositiveShellVariance ε (ε / 2) := by
    unfold upperPositiveShellVariance
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (Continuous.intervalIntegrable (by
        have := positiveShellDensity_continuous ε; fun_prop) _ _)
    · exact (Continuous.intervalIntegrable (by
        have := positiveShellDensity_continuous ε; fun_prop) _ _)
    · intro a _
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hpd a) (sq_nonneg a))
      rw [Real.cosh_le_cosh, abs_mul, abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg a)
      rw [abs_le]; constructor
      · rw [abs_of_pos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
  have hposnn : 0 ≤ upperPositiveShellVariance ε (ε / 2) := by
    unfold upperPositiveShellVariance
    apply intervalIntegral.integral_nonneg (by linarith)
    intro a _
    have := Real.cosh_pos ((1 + ε / 2) * a)
    exact mul_nonneg (mul_nonneg (hpd a) (sq_nonneg a)) this.le
  have hpos2 : upperPositiveShellVariance ε (u - 1) ≤
      (2 + ε / 2) * upperPositiveShellVariance ε (ε / 2) / (1 + u) := by
    rw [le_div_iff₀ hη]
    calc upperPositiveShellVariance ε (u - 1) * (1 + u)
        ≤ upperPositiveShellVariance ε (ε / 2) * (1 + u) :=
          mul_le_mul_of_nonneg_right hposmono hη.le
      _ ≤ upperPositiveShellVariance ε (ε / 2) * (2 + ε / 2) :=
          mul_le_mul_of_nonneg_left (by linarith) hposnn
      _ = _ := by ring
  calc upperGammaVariance ℓ (1 + u) +
        (upperPositiveShellVariance ε (u - 1) - upperShortShellVariance ε (u - 1))
      ≤ (3 / 2) / (1 + u) + (2 + ε / 2) * upperPositiveShellVariance ε (ε / 2) / (1 + u) := by
        linarith
    _ = _ := by ring

