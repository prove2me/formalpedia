-- Prove2me | solution 2 for CohnElkies.norm_saddleShellExponential_eq_exp_neg_damping
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:32:57.29938+00:00
-- url     : https://prove2.me/submissions/a62e6d77-48f2-4b58-b684-dc6831a8a239

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


theorem solution
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ T u : ℝ) :
    ‖Complex.exp
      ((ℓ : ℂ) * mellinShellPhase ε
        ((T : ℂ) + Complex.I * (u : ℂ)))‖ =
      Real.exp (ℓ * realHyperbolicShellPhase ε u) *
        Real.exp
          (-(positiveShellDamping ε ℓ (u - 1) T -
            upperShortShellDamping ε ℓ (u - 1) T)) := by
  have h0 : 0 < shortCutoff ε := by unfold shortCutoff; positivity
  have hsc : ContinuousOn (shortShellDensity ε) (Set.uIcc (shortCutoff ε) (shortEndpoint ε)) := by
    rw [Set.uIcc_of_le horder]
    unfold shortShellDensity shortMargin
    apply ContinuousOn.neg
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro a ha
    have ha0 : 0 < a := lt_of_lt_of_le h0 ha.1
    have := Real.cosh_pos a
    positivity
  have hpc := positiveShellDensity_continuous ε
  have hcosre : ∀ a : ℝ, (Complex.cos ((a : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ)))).re = Real.cos (a * T) * Real.cosh (a * u) := by
    intro a
    rw [show (a : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ)) = ((a * T : ℝ) : ℂ) + ((a * u : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.cos_add_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin, ← Complex.ofReal_sinh]
    simp only [Complex.sub_re, Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, Complex.sub_im, Complex.mul_im, Complex.add_im]
    ring
  have hpt : ∀ a ρ : ℝ, ((ρ : ℂ) * (Complex.cos ((a : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ))) - 1)).re
      = ρ * (Real.cos (a * T) * Real.cosh (a * u) - 1) := by
    intro a ρ
    rw [Complex.re_ofReal_mul, Complex.sub_re, hcosre, Complex.one_re]
  have hi1 : IntervalIntegrable (fun a : ℝ => (shortShellDensity ε a : ℂ) * (Complex.cos ((a : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ))) - 1))
      volume (shortCutoff ε) (shortEndpoint ε) :=
    ((Complex.continuous_ofReal.comp_continuousOn hsc).mul (by fun_prop)).intervalIntegrable
  have hi2 : IntervalIntegrable (fun a : ℝ => (positiveShellDensity ε a : ℂ) * (Complex.cos ((a : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ))) - 1))
      volume (shellLocation ε) (shellLocation ε + 1) :=
    (Continuous.continuousOn (by fun_prop)).intervalIntegrable
  have hphase : (mellinShellPhase ε ((T : ℂ) + Complex.I * (u : ℂ))).re =
      (∫ a in shortCutoff ε..shortEndpoint ε, shortShellDensity ε a * (Real.cos (a * T) * Real.cosh (a * u) - 1)) +
      (∫ a in shellLocation ε..shellLocation ε + 1, positiveShellDensity ε a * (Real.cos (a * T) * Real.cosh (a * u) - 1)) := by
    unfold mellinShellPhase
    rw [Complex.add_re]
    have e1 := (Complex.reCLM.intervalIntegral_comp_comm hi1)
    have e2 := (Complex.reCLM.intervalIntegral_comp_comm hi2)
    simp only [Complex.reCLM_apply] at e1 e2
    rw [← e1, ← e2]
    congr 1
    · exact intervalIntegral.integral_congr (fun a _ => hpt a _)
    · exact intervalIntegral.integral_congr (fun a _ => hpt a _)
  have hs1 : ContinuousOn (fun a => shortShellDensity ε a * (Real.cosh (a * u) - 1)) (Set.uIcc (shortCutoff ε) (shortEndpoint ε)) :=
    hsc.mul (by fun_prop)
  have hs2 : ContinuousOn (fun a => (-shortShellDensity ε a) * Real.cosh ((1 + (u - 1)) * a) * (1 - Real.cos (a * T)))
      (Set.uIcc (shortCutoff ε) (shortEndpoint ε)) :=
    (hsc.neg.mul (by fun_prop)).mul (by fun_prop)
  have hI1 : (∫ a in shortCutoff ε..shortEndpoint ε, shortShellDensity ε a * (Real.cos (a * T) * Real.cosh (a * u) - 1)) =
      (∫ a in shortCutoff ε..shortEndpoint ε, shortShellDensity ε a * (Real.cosh (a * u) - 1)) +
      (∫ a in shortCutoff ε..shortEndpoint ε, (-shortShellDensity ε a) * Real.cosh ((1 + (u - 1)) * a) * (1 - Real.cos (a * T))) := by
    rw [← intervalIntegral.integral_add hs1.intervalIntegrable hs2.intervalIntegrable]
    apply intervalIntegral.integral_congr
    intro a _
    simp only
    rw [show (1 + (u - 1)) * a = a * u by ring]
    ring
  have hI2 : (∫ a in shellLocation ε..shellLocation ε + 1, positiveShellDensity ε a * (Real.cos (a * T) * Real.cosh (a * u) - 1)) =
      (∫ a in shellLocation ε..shellLocation ε + 1, positiveShellDensity ε a * (Real.cosh (a * u) - 1)) -
      (∫ a in shellLocation ε..shellLocation ε + 1, positiveShellDensity ε a * Real.cosh ((1 + (u - 1)) * a) * (1 - Real.cos (a * T))) := by
    rw [← intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)]
    apply intervalIntegral.integral_congr
    intro a _
    simp only
    rw [show (1 + (u - 1)) * a = a * u by ring]
    ring
  rw [Complex.norm_exp, Complex.re_ofReal_mul, hphase, hI1, hI2, ← Real.exp_add]
  unfold realHyperbolicShellPhase positiveShellDamping upperShortShellDamping
  congr 1
  ring

