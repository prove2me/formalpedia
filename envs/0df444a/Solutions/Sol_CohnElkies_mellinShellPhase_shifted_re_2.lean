-- Prove2me | solution 2 for CohnElkies.mellinShellPhase_shifted_re
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:33:39.842107+00:00
-- url     : https://prove2.me/submissions/887e335a-2cfb-4752-b0fb-511d5d4ebc64

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
theorem h47_cre (w : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) (hw : ContinuousOn w (Icc a b)) (T u : ℝ) :
    (∫ x in a..b, (w x : ℂ) * (Complex.cos ((x : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ))) - 1)).re =
      ∫ x in a..b, w x * (Real.cos (x * T) * Real.cosh (x * u) - 1) := by
  have hw' : ContinuousOn w (Set.uIcc a b) := by rw [Set.uIcc_of_le hab]; exact hw
  have hint : IntervalIntegrable (fun x : ℝ => (w x : ℂ) *
      (Complex.cos ((x : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ))) - 1)) MeasureTheory.volume a b :=
    ((Complex.continuous_ofReal.comp_continuousOn hw').mul (by fun_prop)).intervalIntegrable
  rw [← Complex.reCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
  congr 1; funext x
  have e : (x : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ)) = ((x * T : ℝ) : ℂ) + ((x * u : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [Complex.reCLM_apply, e, Complex.cos_add_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sin, ← Complex.ofReal_sinh]
  simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, Complex.sub_im]
  ring

theorem solution
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (T u : ℝ) :
    (mellinShellPhase ε
      ((T : ℂ) + Complex.I * (u : ℂ))).re =
      (∫ a in shortCutoff ε..shortEndpoint ε,
        shortShellDensity ε a *
          (Real.cos (a * T) * Real.cosh (a * u) - 1)) +
      (∫ a in shellLocation ε..shellLocation ε + 1,
        positiveShellDensity ε a *
          (Real.cos (a * T) * Real.cosh (a * u) - 1)) := by
  have hc : 0 < shortCutoff ε := by unfold shortCutoff; positivity
  have hw1 : ContinuousOn (shortShellDensity ε) (Icc (shortCutoff ε) (shortEndpoint ε)) := by
    unfold shortShellDensity shortMargin
    refine ContinuousOn.neg (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)
    intro a ha
    have : 0 < a := lt_of_lt_of_le hc ha.1
    have := Real.cosh_pos a
    positivity
  have hw2 : ContinuousOn (positiveShellDensity ε) (Icc (shellLocation ε) (shellLocation ε + 1)) := by
    unfold positiveShellDensity
    exact (continuous_const.div Real.continuous_cosh (fun a => (Real.cosh_pos a).ne')).continuousOn
  unfold mellinShellPhase
  rw [Complex.add_re, h47_cre _ horder hw1 T u, h47_cre _ (by linarith) hw2 T u]

