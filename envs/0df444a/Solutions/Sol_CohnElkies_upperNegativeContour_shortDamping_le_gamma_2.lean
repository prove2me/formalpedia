-- Prove2me | solution 2 for CohnElkies.upperNegativeContour_shortDamping_le_gamma
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:44:38.143262+00:00
-- url     : https://prove2.me/submissions/500494e0-e7f6-48e0-aa7e-cafabf063a0b

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
theorem h47_smp {ε ℓ κ η a : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (hκ : 1 ≤ κ)
    (hη : 0 < η) (hκη : κ + η ≤ 3)
    (ha : 0 < a)
    (hmargin : 0 ≤ shortMargin ε a) :
    ℓ * (-shortShellDensity ε a) * Real.cosh (κ * a) ≤
      (1 - 4 * ε) * upperGammaMeasureDensity ℓ η a := by
  unfold shortShellDensity upperGammaMeasureDensity
  rw [neg_neg]
  have hca := Real.cosh_pos a
  have hm1 : shortMargin ε a ≤ 1 - 4 * ε := by unfold shortMargin; nlinarith
  have hcosh : Real.cosh (κ * a) / Real.cosh a ≤ Real.exp ((κ - 1) * a) := by
    rw [div_le_iff₀ hca]
    have hb : 0 ≤ (κ - 1) * a := mul_nonneg (by linarith) ha.le
    have hs : 0 ≤ Real.sinh ((κ - 1) * a) := Real.sinh_nonneg_iff.2 hb
    have hsc : Real.sinh a ≤ Real.cosh a := (Real.sinh_lt_cosh a).le
    rw [show κ * a = a + (κ - 1) * a by ring, Real.cosh_add, ← Real.cosh_add_sinh ((κ - 1) * a)]
    nlinarith [Real.cosh_pos ((κ - 1) * a)]
  have hX0 : 0 ≤ Real.cosh (κ * a) / Real.cosh a := div_nonneg (Real.cosh_pos _).le hca.le
  have hexp : Real.exp (-2 * a) * Real.exp ((κ - 1) * a) ≤ Real.exp (-η * a) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith
  have hEX : Real.exp (-2 * a) * (Real.cosh (κ * a) / Real.cosh a) ≤ Real.exp (-η * a) :=
    le_trans (mul_le_mul_of_nonneg_left hcosh (Real.exp_pos _).le) hexp
  have hD1 : 1 - 2 * a / ℓ ≤ Real.exp (-(2 * a / ℓ)) := by linarith [Real.add_one_le_exp (-(2 * a / ℓ))]
  have hD0 : 0 < 1 - Real.exp (-(2 * a / ℓ)) := by
    have : Real.exp (-(2 * a / ℓ)) < 1 := Real.exp_lt_one_iff.mpr (by have := div_pos (by linarith : (0:ℝ) < 2 * a) hℓ; linarith)
    linarith
  have eqL : ℓ * (shortMargin ε a * Real.exp (-2 * a) / (2 * a ^ 2 * Real.cosh a)) * Real.cosh (κ * a)
      = ℓ * shortMargin ε a / (2 * a ^ 2) * (Real.exp (-2 * a) * (Real.cosh (κ * a) / Real.cosh a)) := by
    field_simp <;> ring
  rw [eqL]
  have hk : 0 ≤ ℓ * shortMargin ε a / (2 * a ^ 2) := by positivity
  have hq : ℓ / (2 * a ^ 2) ≤ 1 / (a * (1 - Real.exp (-(2 * a / ℓ)))) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : ℓ * (1 - Real.exp (-(2 * a / ℓ))) ≤ 2 * a := by
      have h := mul_le_mul_of_nonneg_left (show 1 - Real.exp (-(2 * a / ℓ)) ≤ 2 * a / ℓ by linarith) hℓ.le
      rwa [mul_div_cancel₀ _ hℓ.ne'] at h
    nlinarith
  have he := Real.exp_pos (-η * a)
  have h4 : 0 ≤ 1 - 4 * ε := by linarith
  calc ℓ * shortMargin ε a / (2 * a ^ 2) * (Real.exp (-2 * a) * (Real.cosh (κ * a) / Real.cosh a))
      ≤ ℓ * shortMargin ε a / (2 * a ^ 2) * Real.exp (-η * a) := mul_le_mul_of_nonneg_left hEX hk
    _ = shortMargin ε a * (ℓ / (2 * a ^ 2)) * Real.exp (-η * a) := by ring
    _ ≤ (1 - 4 * ε) * (1 / (a * (1 - Real.exp (-(2 * a / ℓ))))) * Real.exp (-η * a) := by
        apply mul_le_mul_of_nonneg_right _ he.le
        exact mul_le_mul hm1 hq (by positivity) h4
    _ = (1 - 4 * ε) * (Real.exp (-η * a) / (a * (1 - Real.exp (-(2 * a / ℓ))))) := by ring

theorem h47_lin_exp_int {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) :
    IntegrableOn (fun a : ℝ => (ℓ + 2 * a) * Real.exp (-η * a)) (Ioi 0) := by
  have hc : 0 < η / 2 := by positivity
  apply integrable_of_isBigO_exp_neg hc (by fun_prop : Continuous (fun a : ℝ => (ℓ + 2 * a) * Real.exp (-η * a))).continuousOn
  have h1 := (isLittleO_pow_exp_pos_mul_atTop 1 hc).bound one_pos
  apply Asymptotics.IsBigO.of_bound (ℓ + 2)
  filter_upwards [h1, eventually_ge_atTop 0] with x hx hx0
  simp only [Real.norm_eq_abs, pow_one] at hx ⊢
  rw [abs_of_nonneg hx0, abs_of_pos (Real.exp_pos _), one_mul] at hx
  rw [abs_of_nonneg (by positivity), abs_of_pos (Real.exp_pos _)]
  have hE1 : 1 ≤ Real.exp (η / 2 * x) := Real.one_le_exp (by positivity)
  have hAB : Real.exp (η / 2 * x) * Real.exp (-(η / 2) * x) = 1 := by
    rw [← Real.exp_add, ← Real.exp_zero]; congr 1; ring
  have hBB : Real.exp (-η * x) = Real.exp (-(η / 2) * x) * Real.exp (-(η / 2) * x) := by
    rw [← Real.exp_add]; congr 1; ring
  have hB := Real.exp_pos (-(η / 2) * x)
  have hpoly : ℓ + 2 * x ≤ (ℓ + 2) * Real.exp (η / 2 * x) := by nlinarith
  rw [hBB]
  have := mul_le_mul_of_nonneg_right hpoly (mul_pos hB hB).le
  have h4 : (ℓ + 2) * Real.exp (η / 2 * x) * (Real.exp (-(η / 2) * x) * Real.exp (-(η / 2) * x)) = (ℓ + 2) * Real.exp (-(η / 2) * x) := by
    rw [mul_assoc, ← mul_assoc (Real.exp (η / 2 * x)), hAB, one_mul]
  linarith

theorem solution
    {ε ℓ κ η : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (hκ : 1 ≤ κ)
    (hη : 0 < η) (hκη : κ + η ≤ 3)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε),
      0 ≤ shortMargin ε a)
    (T : ℝ) :
    upperShortShellDamping ε ℓ (-κ - 1) T ≤
      (1 - 4 * ε) * upperGammaDamping ℓ η T := by
  have h0 : 0 < shortCutoff ε := by unfold shortCutoff; positivity
  have hpos : ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε), 0 < a := fun a ha => lt_of_lt_of_le h0 ha.1
  -- the gamma integrand
  have hD : ∀ a : ℝ, 0 < a → 0 < 1 - Real.exp (-(2 * a / ℓ)) := fun a ha => by
    have : Real.exp (-(2 * a / ℓ)) < 1 := Real.exp_lt_one_iff.mpr (by have := div_pos (by linarith : (0:ℝ) < 2 * a) hℓ; linarith)
    linarith
  have hfnn : ∀ a : ℝ, 0 < a → 0 ≤ upperGammaDampingIntegrand ℓ η T a := fun a ha => by
    unfold upperGammaDampingIntegrand upperGammaMeasureDensity
    have h1 : 0 ≤ 1 - Real.cos (a * T) := by linarith [Real.cos_le_one (a * T)]
    have := hD a ha
    have := Real.exp_pos (-η * a)
    positivity
  have hfc : ContinuousOn (upperGammaDampingIntegrand ℓ η T) (Ioi 0) := by
    unfold upperGammaDampingIntegrand upperGammaMeasureDensity
    apply ContinuousOn.mul (by fun_prop)
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro a ha
    exact (mul_pos (show (0:ℝ) < a from ha) (hD a ha)).ne'
  have hfint : IntegrableOn (upperGammaDampingIntegrand ℓ η T) (Ioi 0) := by
    refine Integrable.mono' ((h47_lin_exp_int hℓ hη).const_mul (T ^ 2 / 4)) (hfc.aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun a ha => ?_)
    have ha0 : (0:ℝ) < a := ha
    rw [Real.norm_of_nonneg (hfnn a ha0)]
    unfold upperGammaDampingIntegrand upperGammaMeasureDensity
    have hc1 : 1 - Real.cos (a * T) ≤ (a * T) ^ 2 / 2 := by linarith [Real.one_sub_sq_div_two_le_cos (x := a * T)]
    have hc0 : 0 ≤ 1 - Real.cos (a * T) := by linarith [Real.cos_le_one (a * T)]
    have hDa := hD a ha0
    have hx : 0 ≤ 2 * a / ℓ := by positivity
    have hex := Real.add_one_le_exp (2 * a / ℓ)
    have hEF : Real.exp (2 * a / ℓ) * Real.exp (-(2 * a / ℓ)) = 1 := by rw [← Real.exp_add]; simp
    have hF := Real.exp_pos (-(2 * a / ℓ))
    have hkey : 2 * a ≤ (ℓ + 2 * a) * (1 - Real.exp (-(2 * a / ℓ))) := by
      have h1 : (2 * a / ℓ + 1) * Real.exp (-(2 * a / ℓ)) ≤ 1 := by nlinarith
      have h2 : ℓ * (2 * a / ℓ) = 2 * a := by field_simp
      nlinarith
    have hinv : 1 / (a * (1 - Real.exp (-(2 * a / ℓ)))) ≤ (ℓ + 2 * a) / (2 * a ^ 2) := by
      rw [div_le_div_iff₀ (mul_pos ha0 hDa) (by positivity)]
      nlinarith
    have he := Real.exp_pos (-η * a)
    calc (1 - Real.cos (a * T)) * (Real.exp (-η * a) / (a * (1 - Real.exp (-(2 * a / ℓ)))))
        = (1 - Real.cos (a * T)) * Real.exp (-η * a) * (1 / (a * (1 - Real.exp (-(2 * a / ℓ))))) := by ring
      _ ≤ ((a * T) ^ 2 / 2) * Real.exp (-η * a) * ((ℓ + 2 * a) / (2 * a ^ 2)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hc1 he.le) hinv (by positivity) (by positivity)
      _ = T ^ 2 / 4 * ((ℓ + 2 * a) * Real.exp (-η * a)) := by field_simp <;> ring
  -- main estimate
  have hγc : ContinuousOn (fun a => (1 - 4 * ε) * upperGammaDampingIntegrand ℓ η T a)
      (uIcc (shortCutoff ε) (shortEndpoint ε)) := by
    apply ContinuousOn.mul continuousOn_const
    apply hfc.mono
    intro a ha
    rw [uIcc_of_le horder] at ha
    exact hpos a ha
  have hsc : ContinuousOn (fun a => (-shortShellDensity ε a) * Real.cosh ((1 + (-κ - 1)) * a) * (1 - Real.cos (a * T)))
      (uIcc (shortCutoff ε) (shortEndpoint ε)) := by
    rw [uIcc_of_le horder]
    unfold shortShellDensity shortMargin
    apply ContinuousOn.mul (ContinuousOn.mul (ContinuousOn.neg (ContinuousOn.neg ?_)) (by fun_prop)) (by fun_prop)
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro a ha
    have ha0 := hpos a ha
    have := Real.cosh_pos a
    positivity
  unfold upperShortShellDamping upperGammaDamping
  rw [← intervalIntegral.integral_const_mul]
  calc (∫ a in shortCutoff ε..shortEndpoint ε, ℓ * ((-shortShellDensity ε a) * Real.cosh ((1 + (-κ - 1)) * a) * (1 - Real.cos (a * T))))
      ≤ ∫ a in shortCutoff ε..shortEndpoint ε, (1 - 4 * ε) * upperGammaDampingIntegrand ℓ η T a := by
        apply intervalIntegral.integral_mono_on horder (hsc.const_mul ℓ |>.intervalIntegrable) hγc.intervalIntegrable
        intro a ha
        have ha0 := hpos a ha
        have hp := h47_smp hε hεsmall hℓ hκ hη hκη ha0 (hmargin a ha)
        have hc0 : 0 ≤ 1 - Real.cos (a * T) := by linarith [Real.cos_le_one (a * T)]
        rw [show (1 + (-κ - 1)) * a = -(κ * a) by ring, Real.cosh_neg]
        unfold upperGammaDampingIntegrand
        have := mul_le_mul_of_nonneg_right hp hc0
        linarith
    _ = (1 - 4 * ε) * ∫ a in Ioc (shortCutoff ε) (shortEndpoint ε), upperGammaDampingIntegrand ℓ η T a := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le horder]
    _ ≤ (1 - 4 * ε) * ∫ a in Ioi 0, upperGammaDampingIntegrand ℓ η T a := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        apply setIntegral_mono_set hfint
        · exact (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun a ha => hfnn a ha)
        · exact HasSubset.Subset.eventuallyLE (fun a ha => (show a ∈ Ioi (0:ℝ) from lt_trans h0 ha.1))

