-- Prove2me | solution 2 for CohnElkies.upperShortShellDamping_global_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:29:07.557042+00:00
-- url     : https://prove2.me/submissions/e600f18b-1e70-4c09-8fc6-14c15b7136f8

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
theorem h47_ssd_le {ε δ a A : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) (ha : 0 < a) (haA : a ≤ A) :
    (-shortShellDensity ε a) * a ^ 2 * Real.cosh ((1 + δ) * a) ≤ (1 / 2 : ℝ) * Real.exp (δ * A) := by
  unfold shortShellDensity
  rw [neg_neg]
  have hca := Real.cosh_pos a
  have hm : shortMargin ε a ≤ 1 := by unfold shortMargin; nlinarith
  have he : Real.exp (-2 * a) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have he0 := Real.exp_pos (-2 * a)
  have hme : shortMargin ε a * Real.exp (-2 * a) ≤ 1 := by
    rcases le_total 0 (shortMargin ε a) with h | h
    · nlinarith
    · nlinarith
  have hcosh : Real.cosh ((1 + δ) * a) ≤ Real.cosh a * Real.exp (δ * A) := by
    have hb : 0 ≤ δ * a := mul_nonneg hδ ha.le
    have hs : 0 ≤ Real.sinh (δ * a) := Real.sinh_nonneg_iff.2 hb
    have hsc : Real.sinh a ≤ Real.cosh a := (Real.sinh_lt_cosh a).le
    have hex : Real.exp (δ * a) ≤ Real.exp (δ * A) := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left haA hδ)
    rw [show (1 + δ) * a = a + δ * a by ring, Real.cosh_add]
    have hcb := Real.cosh_pos (δ * a)
    have h1 : Real.cosh a * Real.cosh (δ * a) + Real.sinh a * Real.sinh (δ * a) ≤ Real.cosh a * Real.exp (δ * a) := by
      rw [← Real.cosh_add_sinh (δ * a)]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hex hca.le]
  have hr0 : 0 ≤ Real.cosh ((1 + δ) * a) / Real.cosh a := div_nonneg (Real.cosh_pos _).le hca.le
  have hr : Real.cosh ((1 + δ) * a) / Real.cosh a ≤ Real.exp (δ * A) := by
    rw [div_le_iff₀ hca]; linarith
  have eq : shortMargin ε a * Real.exp (-2 * a) / (2 * a ^ 2 * Real.cosh a) * a ^ 2 * Real.cosh ((1 + δ) * a)
      = (shortMargin ε a * Real.exp (-2 * a)) * (Real.cosh ((1 + δ) * a) / Real.cosh a) / 2 := by
    field_simp <;> ring
  rw [eq]
  nlinarith [mul_le_mul_of_nonneg_right hme hr0]

theorem solution
    {ε ℓ δ T : ℝ}
    (hε : 0 < ε) (hℓ : 0 ≤ ℓ) (hδ : 0 ≤ δ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Set.Icc (shortCutoff ε)
      (shortEndpoint ε), 0 ≤ shortMargin ε a) :
    upperShortShellDamping ε ℓ δ T ≤
      ℓ * upperShellShortCoefficient ε *
        Real.exp (δ * shortEndpoint ε) *
          min (T ^ 2) 1 := by
  have h0 : 0 < shortCutoff ε := by unfold shortCutoff; positivity
  have hE0 : 0 < shortEndpoint ε := lt_of_lt_of_le h0 horder
  have hK := Real.exp_pos (δ * shortEndpoint ε)
  have hP : ∀ a ∈ Set.Icc (shortCutoff ε) (shortEndpoint ε),
      0 ≤ (-shortShellDensity ε a) * Real.cosh ((1 + δ) * a) ∧
      (-shortShellDensity ε a) * Real.cosh ((1 + δ) * a) * a ^ 2 ≤ Real.exp (δ * shortEndpoint ε) / 2 := by
    intro a ha
    have ha0 : 0 < a := lt_of_lt_of_le h0 ha.1
    have hm := hmargin a ha
    constructor
    · unfold shortShellDensity
      rw [neg_neg]
      have := Real.cosh_pos a
      exact mul_nonneg (div_nonneg (mul_nonneg hm (Real.exp_pos _).le) (by positivity)) (Real.cosh_pos _).le
    · have := h47_ssd_le (δ := δ) hε hδ ha0 ha.2
      linarith [show (-shortShellDensity ε a) * Real.cosh ((1 + δ) * a) * a ^ 2 = (-shortShellDensity ε a) * a ^ 2 * Real.cosh ((1 + δ) * a) by ring]
  have hcont : ContinuousOn (fun a => (-shortShellDensity ε a) * Real.cosh ((1 + δ) * a) * (1 - Real.cos (a * T)))
      (Set.uIcc (shortCutoff ε) (shortEndpoint ε)) := by
    rw [Set.uIcc_of_le horder]
    unfold shortShellDensity shortMargin
    apply ContinuousOn.mul (ContinuousOn.mul (ContinuousOn.neg (ContinuousOn.neg ?_)) (by fun_prop)) (by fun_prop)
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro a ha
    have ha0 : 0 < a := lt_of_lt_of_le h0 ha.1
    have := Real.cosh_pos a
    positivity
  unfold upperShortShellDamping upperShellShortCoefficient
  rcases le_total (T ^ 2) 1 with hT | hT
  · rw [min_eq_left hT]
    have hI : (∫ a in shortCutoff ε..shortEndpoint ε, (-shortShellDensity ε a) * Real.cosh ((1 + δ) * a) * (1 - Real.cos (a * T)))
        ≤ ∫ a in shortCutoff ε..shortEndpoint ε, Real.exp (δ * shortEndpoint ε) * T ^ 2 / 4 := by
      apply intervalIntegral.integral_mono_on horder hcont.intervalIntegrable intervalIntegrable_const
      intro a ha
      obtain ⟨hp0, hp1⟩ := hP a ha
      have hc1 : 1 - Real.cos (a * T) ≤ (a * T) ^ 2 / 2 := by linarith [Real.one_sub_sq_div_two_le_cos (x := a * T)]
      have hc0 : 0 ≤ 1 - Real.cos (a * T) := by linarith [Real.cos_le_one (a * T)]
      have := mul_le_mul_of_nonneg_left hc1 hp0
      have hT0 : 0 ≤ T ^ 2 := sq_nonneg T
      nlinarith [mul_le_mul_of_nonneg_right hp1 hT0]
    rw [intervalIntegral.integral_const, smul_eq_mul] at hI
    have hci : 0 < (shortCutoff ε)⁻¹ := inv_pos.2 h0
    have h2 : (shortEndpoint ε - shortCutoff ε) * (Real.exp (δ * shortEndpoint ε) * T ^ 2 / 4)
        ≤ (shortEndpoint ε + (shortCutoff ε)⁻¹) * Real.exp (δ * shortEndpoint ε) * T ^ 2 := by
      have hT0 : 0 ≤ Real.exp (δ * shortEndpoint ε) * T ^ 2 := by positivity
      nlinarith
    calc ℓ * (∫ a in shortCutoff ε..shortEndpoint ε, (-shortShellDensity ε a) * Real.cosh ((1 + δ) * a) * (1 - Real.cos (a * T)))
        ≤ ℓ * ((shortEndpoint ε + (shortCutoff ε)⁻¹) * Real.exp (δ * shortEndpoint ε) * T ^ 2) :=
          mul_le_mul_of_nonneg_left (hI.trans h2) hℓ
      _ = _ := by ring
  · rw [min_eq_right hT]
    have hne : ∀ a ∈ Set.uIcc (shortCutoff ε) (shortEndpoint ε), a ≠ 0 := by
      intro a ha; rw [Set.uIcc_of_le horder] at ha; exact (lt_of_lt_of_le h0 ha.1).ne'
    have hderiv : ∀ a ∈ Set.uIcc (shortCutoff ε) (shortEndpoint ε),
        HasDerivAt (fun y : ℝ => -Real.exp (δ * shortEndpoint ε) * y⁻¹) (Real.exp (δ * shortEndpoint ε) * (a ^ 2)⁻¹) a := by
      intro a ha
      exact ((hasDerivAt_inv (hne a ha)).const_mul (-Real.exp (δ * shortEndpoint ε))).congr_deriv (by ring)
    have hgc : ContinuousOn (fun a : ℝ => Real.exp (δ * shortEndpoint ε) * (a ^ 2)⁻¹) (Set.uIcc (shortCutoff ε) (shortEndpoint ε)) :=
      ContinuousOn.mul continuousOn_const (ContinuousOn.inv₀ (by fun_prop) (fun a ha => pow_ne_zero 2 (hne a ha)))
    have hI : (∫ a in shortCutoff ε..shortEndpoint ε, (-shortShellDensity ε a) * Real.cosh ((1 + δ) * a) * (1 - Real.cos (a * T)))
        ≤ ∫ a in shortCutoff ε..shortEndpoint ε, Real.exp (δ * shortEndpoint ε) * (a ^ 2)⁻¹ := by
      apply intervalIntegral.integral_mono_on horder hcont.intervalIntegrable hgc.intervalIntegrable
      intro a ha
      obtain ⟨hp0, hp1⟩ := hP a ha
      have ha0 : 0 < a := lt_of_lt_of_le h0 ha.1
      have hc0 : 1 - Real.cos (a * T) ≤ 2 := by linarith [Real.neg_one_le_cos (a * T)]
      have h1 := mul_le_mul_of_nonneg_left hc0 hp0
      have ha2 : 0 < a ^ 2 := by positivity
      have : (-shortShellDensity ε a) * Real.cosh ((1 + δ) * a) ≤ Real.exp (δ * shortEndpoint ε) / 2 * (a ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ ha2]; exact hp1
      nlinarith
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hgc.intervalIntegrable] at hI
    have hci : 0 < (shortCutoff ε)⁻¹ := inv_pos.2 h0
    have hEi : 0 < (shortEndpoint ε)⁻¹ := inv_pos.2 hE0
    have h2 : -Real.exp (δ * shortEndpoint ε) * (shortEndpoint ε)⁻¹ - -Real.exp (δ * shortEndpoint ε) * (shortCutoff ε)⁻¹
        ≤ (shortEndpoint ε + (shortCutoff ε)⁻¹) * Real.exp (δ * shortEndpoint ε) := by
      nlinarith [mul_pos hK hEi]
    calc ℓ * (∫ a in shortCutoff ε..shortEndpoint ε, (-shortShellDensity ε a) * Real.cosh ((1 + δ) * a) * (1 - Real.cos (a * T)))
        ≤ ℓ * ((shortEndpoint ε + (shortCutoff ε)⁻¹) * Real.exp (δ * shortEndpoint ε)) :=
          mul_le_mul_of_nonneg_left (hI.trans h2) hℓ
      _ = _ := by ring

