-- Prove2me | solution 2 for CohnElkies.upperShortShellVariance_global_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:20:32.64116+00:00
-- url     : https://prove2.me/submissions/80d7ef5a-5ae9-4484-b995-967856f4ce7b

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
    {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 ≤ δ)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    upperShortShellVariance ε δ ≤
      (1 / 2 : ℝ) * upperShellShortCoefficient ε *
        Real.exp (δ * shortEndpoint ε) := by
  have h0 : 0 < shortCutoff ε := by unfold shortCutoff; positivity
  unfold upperShortShellVariance upperShellShortCoefficient
  have hcont : ContinuousOn (fun a => (-shortShellDensity ε a) * a ^ 2 * Real.cosh ((1 + δ) * a))
      (Set.uIcc (shortCutoff ε) (shortEndpoint ε)) := by
    rw [Set.uIcc_of_le horder]
    unfold shortShellDensity shortMargin
    apply ContinuousOn.mul (ContinuousOn.mul (ContinuousOn.neg (ContinuousOn.neg ?_)) (by fun_prop)) (by fun_prop)
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro a ha
    have ha0 : 0 < a := lt_of_lt_of_le h0 ha.1
    have := Real.cosh_pos a
    positivity
  calc (∫ a in shortCutoff ε..shortEndpoint ε, (-shortShellDensity ε a) * a ^ 2 * Real.cosh ((1 + δ) * a))
      ≤ ∫ a in shortCutoff ε..shortEndpoint ε, (1 / 2 : ℝ) * Real.exp (δ * shortEndpoint ε) := by
        apply intervalIntegral.integral_mono_on horder (hcont.intervalIntegrable) intervalIntegrable_const
        intro a ha
        exact h47_ssd_le hε hδ (lt_of_lt_of_le h0 ha.1) ha.2
    _ = (shortEndpoint ε - shortCutoff ε) * ((1 / 2 : ℝ) * Real.exp (δ * shortEndpoint ε)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ (1 / 2 : ℝ) * (shortEndpoint ε + (shortCutoff ε)⁻¹) * Real.exp (δ * shortEndpoint ε) := by
        have := Real.exp_pos (δ * shortEndpoint ε)
        have : 0 < (shortCutoff ε)⁻¹ := inv_pos.2 h0
        nlinarith

