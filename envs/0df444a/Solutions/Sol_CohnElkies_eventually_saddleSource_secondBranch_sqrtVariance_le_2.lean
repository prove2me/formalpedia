-- Prove2me | solution 2 for CohnElkies.eventually_saddleSource_secondBranch_sqrtVariance_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:29:49.63598+00:00
-- url     : https://prove2.me/submissions/3f6a2f2c-71f3-48bd-a313-2655aa06e9f9

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

theorem h48_var2_ev : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ℓ : ℝ, 1 ≤ ℓ →
        ∀ δ : ℝ, ε / 2 ≤ δ →
          saddleSourceGaussianVariance ε ℓ (1 + δ) ≤
            saddleSourceSecondBranchVarianceCoefficient ε *
              Real.exp
                ((shellLocation ε + 1) * δ) := by
  filter_upwards [self_mem_nhdsWithin, h48_margin_ev, eventually_upper_shortCutoff_le_shortEndpoint]
    with ε hε hmargin horder
  have hε0 : 0 < ε := hε
  intro ℓ hℓ δ hδ
  have hδ0 : 0 ≤ δ := by linarith
  have hc0 : 0 < shortCutoff ε := by unfold shortCutoff; positivity
  unfold saddleSourceGaussianVariance upperSaddleVariance upperNetShellVariance
    saddleSourceSecondBranchVarianceCoefficient
  rw [show 1 + δ - 1 = δ by ring]
  have hg := h48_gvar_le ℓ (2 + δ) (by linarith) (by linarith) (by nlinarith)
  have hg' : upperGammaVariance ℓ (2 + δ) ≤ 2 := by
    refine hg.trans ?_; rw [div_le_iff₀ (by linarith)]; nlinarith
  have hshort : 0 ≤ upperShortShellVariance ε δ := by
    unfold upperShortShellVariance
    apply intervalIntegral.integral_nonneg horder
    intro a ha
    have ha0 : 0 < a := hc0.trans_le ha.1
    have hm := hmargin a ha
    have h1 : 0 ≤ -shortShellDensity ε a := by
      unfold shortShellDensity; rw [neg_neg]; have := Real.cosh_pos a; positivity
    have := Real.cosh_pos ((1 + δ) * a)
    positivity
  set L := shellLocation ε with hL
  have hL0 : 0 < L := by rw [hL]; unfold shellLocation; positivity
  set w := shellWeight ε with hw
  have hw0 : 0 < w := shellWeight_pos ε
  set B := (L + 1) ^ 2 * w * Real.exp ((L + 1) * δ) with hB
  have hpos : upperPositiveShellVariance ε δ ≤ B := by
    unfold upperPositiveShellVariance
    have hconst : (∫ a in L..L + 1, B) = B := by simp
    rw [← hconst]
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (Continuous.intervalIntegrable (by
        have := positiveShellDensity_continuous ε; fun_prop) _ _)
    · exact intervalIntegrable_const
    · intro a ha
      have ha0 : 0 < a := hL0.trans_le ha.1
      unfold positiveShellDensity
      rw [← hw]
      have hcosh : Real.cosh ((1 + δ) * a) ≤ Real.exp (δ * a) * Real.cosh a := by
        rw [Real.cosh_eq, Real.cosh_eq]
        have e1 : Real.exp ((1 + δ) * a) = Real.exp (δ * a) * Real.exp a := by
          rw [← Real.exp_add]; ring_nf
        have e2 : Real.exp (-((1 + δ) * a)) ≤ Real.exp (δ * a) * Real.exp (-a) := by
          rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
        rw [e1]; nlinarith [Real.exp_pos (δ * a)]
      have hca := Real.cosh_pos a
      have hexp : Real.exp (δ * a) ≤ Real.exp ((L + 1) * δ) := by
        apply Real.exp_le_exp.mpr; nlinarith [ha.2]
      have ha2 : a ^ 2 ≤ (L + 1) ^ 2 := pow_le_pow_left₀ ha0.le ha.2 2
      calc w / Real.cosh a * a ^ 2 * Real.cosh ((1 + δ) * a)
          ≤ w / Real.cosh a * a ^ 2 * (Real.exp (δ * a) * Real.cosh a) := by
            apply mul_le_mul_of_nonneg_left hcosh; positivity
        _ = w * a ^ 2 * Real.exp (δ * a) := by field_simp
        _ ≤ w * (L + 1) ^ 2 * Real.exp ((L + 1) * δ) := by gcongr
        _ = B := by rw [hB]; ring
  have he : 1 ≤ Real.exp ((L + 1) * δ) := Real.one_le_exp (by positivity)
  have : (2 + (L + 1) ^ 2 * w) * Real.exp ((L + 1) * δ) = 2 * Real.exp ((L + 1) * δ) + B := by
    rw [hB]; ring
  rw [this]
  linarith

theorem solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ℓ : ℝ, 1 ≤ ℓ →
        ∀ δ : ℝ, ε / 2 ≤ δ →
          Real.sqrt
              (ℓ * saddleSourceGaussianVariance
                ε ℓ (1 + δ)) ≤
            Real.sqrt
                (saddleSourceSecondBranchVarianceCoefficient ε) *
              Real.sqrt ℓ *
                Real.exp
                  (((shellLocation ε + 1) / 2) * δ) := by
  filter_upwards [h48_var2_ev] with ε h
  intro ℓ hℓ δ hδ
  have hv := h ℓ hℓ δ hδ
  have hℓ0 : 0 ≤ ℓ := by linarith
  calc Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ))
      ≤ Real.sqrt (ℓ * (saddleSourceSecondBranchVarianceCoefficient ε *
          Real.exp ((shellLocation ε + 1) * δ))) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hv hℓ0)
    _ = Real.sqrt (saddleSourceSecondBranchVarianceCoefficient ε) * Real.sqrt ℓ *
          Real.exp (((shellLocation ε + 1) / 2) * δ) := by
        have hco : 0 ≤ saddleSourceSecondBranchVarianceCoefficient ε := by
          unfold saddleSourceSecondBranchVarianceCoefficient
          have := shellWeight_pos ε; positivity
        rw [show ℓ * (saddleSourceSecondBranchVarianceCoefficient ε *
          Real.exp ((shellLocation ε + 1) * δ)) = saddleSourceSecondBranchVarianceCoefficient ε * ℓ *
          Real.exp ((shellLocation ε + 1) * δ) by ring]
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hco]
        congr 1
        rw [show (shellLocation ε + 1) * δ = ((shellLocation ε + 1) / 2) * δ + ((shellLocation ε + 1) / 2) * δ by ring,
          Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le]

