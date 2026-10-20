-- Prove2me | solution 2 for CohnElkies.saddleSourceShellQuadraticRemainder_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:54:45.685234+00:00
-- url     : https://prove2.me/submissions/7eb329f5-6b13-4c12-afe1-578b530efcd7

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
theorem h47b_q (w : ℝ → ℝ) (hw : Continuous w) (lo hi u T : ℝ) :
    ∫ a in lo..hi, (w a : ℂ) * saddleSourceCosineQuadraticRemainder a u T =
      (∫ a in lo..hi, (w a : ℂ) * (Complex.cos ((a : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ))) - 1)) -
        ((∫ a in lo..hi, w a * (Real.cosh (a * u) - 1) : ℝ) : ℂ) +
        Complex.I * ((T * ∫ a in lo..hi, w a * a * Real.sinh (u * a) : ℝ) : ℂ) +
        ((T ^ 2 / 2 * ∫ a in lo..hi, w a * a ^ 2 * Real.cosh (u * a) : ℝ) : ℂ) := by
  have e1 : ((∫ a in lo..hi, w a * (Real.cosh (a * u) - 1) : ℝ) : ℂ) =
      ∫ a in lo..hi, ((w a * (Real.cosh (a * u) - 1) : ℝ) : ℂ) := (intervalIntegral.integral_ofReal).symm
  have e2 : ((∫ a in lo..hi, w a * a * Real.sinh (u * a) : ℝ) : ℂ) =
      ∫ a in lo..hi, ((w a * a * Real.sinh (u * a) : ℝ) : ℂ) := (intervalIntegral.integral_ofReal).symm
  have e3 : ((∫ a in lo..hi, w a * a ^ 2 * Real.cosh (u * a) : ℝ) : ℂ) =
      ∫ a in lo..hi, ((w a * a ^ 2 * Real.cosh (u * a) : ℝ) : ℂ) := (intervalIntegral.integral_ofReal).symm
  have i0 : IntervalIntegrable (fun a : ℝ => (w a : ℂ) * (Complex.cos ((a : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ))) - 1)) MeasureTheory.volume lo hi :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have i1 : IntervalIntegrable (fun a : ℝ => ((w a * (Real.cosh (a * u) - 1) : ℝ) : ℂ)) MeasureTheory.volume lo hi :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun a : ℝ => Complex.I * ((T : ℂ) * ((w a * a * Real.sinh (u * a) : ℝ) : ℂ))) MeasureTheory.volume lo hi :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun a : ℝ => ((T ^ 2 / 2 : ℝ) : ℂ) * ((w a * a ^ 2 * Real.cosh (u * a) : ℝ) : ℂ)) MeasureTheory.volume lo hi :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have hsplit : ∫ a in lo..hi, (w a : ℂ) * saddleSourceCosineQuadraticRemainder a u T =
      ∫ a in lo..hi, (((w a : ℂ) * (Complex.cos ((a : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ))) - 1)) -
        ((w a * (Real.cosh (a * u) - 1) : ℝ) : ℂ) +
        Complex.I * ((T : ℂ) * ((w a * a * Real.sinh (u * a) : ℝ) : ℂ)) +
        ((T ^ 2 / 2 : ℝ) : ℂ) * ((w a * a ^ 2 * Real.cosh (u * a) : ℝ) : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro a _
    simp only [saddleSourceCosineQuadraticRemainder]
    rw [mul_comm a u]
    push_cast
    ring
  rw [hsplit, intervalIntegral.integral_add ((i0.sub i1).add i2) i3, intervalIntegral.integral_add (i0.sub i1) i2,
    intervalIntegral.integral_sub i0 i1, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, e1, Complex.ofReal_mul T, Complex.ofReal_mul (T ^ 2 / 2), e2, e3]

theorem solution
    {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (u T : ℝ) :
    saddleSourceShellQuadraticRemainder ε u T =
      mellinShellPhase ε
          ((T : ℂ) + Complex.I * (u : ℂ)) -
        (realHyperbolicShellPhase ε u : ℂ) +
        Complex.I *
          ((T * saddleSourceShellDerivative ε u : ℝ) : ℂ) +
        ((T ^ 2 / 2 *
          upperNetShellVariance ε (u - 1) : ℝ) : ℂ) := by
  have hlo : 0 < shortCutoff ε := by unfold shortCutoff; positivity
  let w : ℝ → ℝ := fun a => shortShellDensity ε (max a (shortCutoff ε))
  have hw : Continuous w := by
    have hpos : ∀ a, max a (shortCutoff ε) ≠ 0 := fun a => (lt_of_lt_of_le hlo (le_max_right _ _)).ne'
    show Continuous fun a => -(shortMargin ε (max a (shortCutoff ε)) * Real.exp (-2 * max a (shortCutoff ε)) /
      (2 * (max a (shortCutoff ε)) ^ 2 * Real.cosh (max a (shortCutoff ε))))
    unfold shortMargin
    refine Continuous.neg (Continuous.div (by fun_prop) (by fun_prop) ?_)
    intro a
    have := hpos a
    have := Real.cosh_pos (max a (shortCutoff ε))
    positivity
  have hwp : Continuous (positiveShellDensity ε) := by
    unfold positiveShellDensity
    exact continuous_const.div Real.continuous_cosh (fun a => (Real.cosh_pos a).ne')
  have hcongR : ∀ (F : ℝ → ℝ), ∫ a in shortCutoff ε..shortEndpoint ε, shortShellDensity ε a * F a =
      ∫ a in shortCutoff ε..shortEndpoint ε, w a * F a := by
    intro F
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le horder] at hx
    simp only [w, max_eq_left hx.1]
  have hcongC : ∀ (F : ℝ → ℂ), ∫ a in shortCutoff ε..shortEndpoint ε, (shortShellDensity ε a : ℂ) * F a =
      ∫ a in shortCutoff ε..shortEndpoint ε, (w a : ℂ) * F a := by
    intro F
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le horder] at hx
    simp only [w, max_eq_left hx.1]
  have hcongR' : ∀ (F : ℝ → ℝ), ∫ a in shortCutoff ε..shortEndpoint ε, (-shortShellDensity ε a) * F a =
      -∫ a in shortCutoff ε..shortEndpoint ε, w a * F a := by
    intro F
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le horder] at hx
    simp only [w, max_eq_left hx.1]
    ring
  unfold saddleSourceShellQuadraticRemainder mellinShellPhase realHyperbolicShellPhase saddleSourceShellDerivative
    upperNetShellVariance upperPositiveShellVariance upperShortShellVariance
  have hc : ∀ a : ℝ, Real.cosh ((1 + (u - 1)) * a) = Real.cosh (u * a) := fun a => by ring_nf
  simp only [hc]
  simp only [mul_assoc] at hcongR hcongR' ⊢
  rw [hcongC, hcongC, hcongR, hcongR, hcongR']
  simp only [← mul_assoc]
  rw [h47b_q w hw, h47b_q _ hwp]
  push_cast
  ring

