-- Prove2me | solution 2 for CohnElkies.saddleShellPhase_damping_identity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:54:43.584991+00:00
-- url     : https://prove2.me/submissions/adaa394d-f8a6-4ecc-b4b0-0eb157553ac1

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
theorem h48_re_int (ρ : ℝ → ℝ) (x y : ℝ) (hρ : IntervalIntegrable ρ volume x y) (T u : ℝ) :
    (∫ a in x..y, (ρ a : ℂ) * (Complex.cos ((a : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ))) - 1)).re =
      ∫ a in x..y, ρ a * (Real.cos (a * T) * Real.cosh (a * u) - 1) := by
  have hc : IntervalIntegrable (fun a : ℝ => (ρ a : ℂ)) volume x y := by
    rw [intervalIntegrable_iff] at hρ ⊢
    exact hρ.ofReal
  have hi : IntervalIntegrable (fun a : ℝ => (ρ a : ℂ) *
      (Complex.cos ((a : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ))) - 1)) volume x y := by
    apply hc.mul_continuousOn
    exact Continuous.continuousOn (by fun_prop)
  have := intervalIntegral.intervalIntegral_re hi
  simp only [RCLike.re_to_complex] at this
  rw [← this]
  apply intervalIntegral.integral_congr
  intro a _
  have hz : (a : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ)) = ((a * T : ℝ) : ℂ) + ((a * u : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  simp only
  rw [hz, Complex.cos_add_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin,
    ← Complex.ofReal_sinh]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.one_re, Complex.sub_im, Complex.one_im]
  ring

theorem h48_diff (ρ : ℝ → ℝ) (x y : ℝ) (hρ : IntervalIntegrable ρ volume x y) (T u : ℝ) :
    (∫ a in x..y, ρ a * (Real.cosh (a * u) - 1)) -
      (∫ a in x..y, ρ a * (Real.cos (a * T) * Real.cosh (a * u) - 1)) =
      ∫ a in x..y, ρ a * Real.cosh ((1 + (u - 1)) * a) * (1 - Real.cos (a * T)) := by
  rw [← intervalIntegral.integral_sub]
  · apply intervalIntegral.integral_congr
    intro a _
    simp only
    rw [show (1 + (u - 1)) * a = a * u by ring]
    ring
  · exact hρ.mul_continuousOn (Continuous.continuousOn (by fun_prop))
  · exact hρ.mul_continuousOn (Continuous.continuousOn (by fun_prop))

theorem solution
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ T u : ℝ) :
    ℓ *
      (realHyperbolicShellPhase ε u -
        (mellinShellPhase ε
          ((T : ℂ) + Complex.I * (u : ℂ))).re) =
      positiveShellDamping ε ℓ (u - 1) T -
        upperShortShellDamping ε ℓ (u - 1) T := by
  have hs := shortShellDensity_intervalIntegrable hε horder
  have hp : IntervalIntegrable (positiveShellDensity ε) volume
      (shellLocation ε) (shellLocation ε + 1) :=
    (positiveShellDensity_continuous ε).intervalIntegrable _ _
  have hre : (mellinShellPhase ε ((T : ℂ) + Complex.I * (u : ℂ))).re =
      (∫ a in shortCutoff ε..shortEndpoint ε,
        shortShellDensity ε a * (Real.cos (a * T) * Real.cosh (a * u) - 1)) +
      (∫ a in shellLocation ε..shellLocation ε + 1,
        positiveShellDensity ε a * (Real.cos (a * T) * Real.cosh (a * u) - 1)) := by
    unfold mellinShellPhase
    rw [Complex.add_re, h48_re_int _ _ _ hs, h48_re_int _ _ _ hp]
  rw [hre]
  unfold realHyperbolicShellPhase positiveShellDamping upperShortShellDamping
  have e1 := h48_diff _ _ _ hs T u
  have e2 := h48_diff _ _ _ hp T u
  have e3 : (∫ a in shortCutoff ε..shortEndpoint ε,
      (-shortShellDensity ε a) * Real.cosh ((1 + (u - 1)) * a) * (1 - Real.cos (a * T))) =
      -∫ a in shortCutoff ε..shortEndpoint ε,
        shortShellDensity ε a * Real.cosh ((1 + (u - 1)) * a) * (1 - Real.cos (a * T)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro a _
    simp only
    ring
  rw [e3]
  linear_combination ℓ * e1 + ℓ * e2

