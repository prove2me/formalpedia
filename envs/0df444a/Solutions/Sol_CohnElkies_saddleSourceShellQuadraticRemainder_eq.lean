-- Prove2me | solution 1 for CohnElkies.saddleSourceShellQuadraticRemainder_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/0a605daf-8e1d-4cf0-819c-05322e37accb

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_shortShellDensity_continuousOn_support
import Theorems.Thm_CohnElkies_saddleSourceWeightedCosineQuadraticRemainder_integral_eq

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
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
  let Fs : ℂ :=
    ∫ a in shortCutoff ε..shortEndpoint ε,
      (shortShellDensity ε a : ℂ) *
        (Complex.cos
          ((a : ℂ) *
            ((T : ℂ) + Complex.I * (u : ℂ))) - 1)
  let Fp : ℂ :=
    ∫ a in shellLocation ε..shellLocation ε + 1,
      (positiveShellDensity ε a : ℂ) *
        (Complex.cos
          ((a : ℂ) *
            ((T : ℂ) + Complex.I * (u : ℂ))) - 1)
  let Hs : ℂ :=
    ∫ a in shortCutoff ε..shortEndpoint ε,
      (shortShellDensity ε a : ℂ) *
        ((Real.cosh (u * a) : ℂ) - 1)
  let Hp : ℂ :=
    ∫ a in shellLocation ε..shellLocation ε + 1,
      (positiveShellDensity ε a : ℂ) *
        ((Real.cosh (u * a) : ℂ) - 1)
  let Ls : ℝ :=
    ∫ a in shortCutoff ε..shortEndpoint ε,
      shortShellDensity ε a * a * Real.sinh (u * a)
  let Lp : ℝ :=
    ∫ a in shellLocation ε..shellLocation ε + 1,
      positiveShellDensity ε a * a * Real.sinh (u * a)
  let Vs : ℝ := upperShortShellVariance ε (u - 1)
  let Vp : ℝ := upperPositiveShellVariance ε (u - 1)
  have hshort :=
    saddleSourceWeightedCosineQuadraticRemainder_integral_eq
      (shortShellDensity ε) horder
      (shortShellDensity_continuousOn_support hε) u T
  have hpositive :=
    saddleSourceWeightedCosineQuadraticRemainder_integral_eq
      (positiveShellDensity ε)
      (show shellLocation ε ≤ shellLocation ε + 1 by
        linarith)
      (positiveShellDensity_continuous ε).continuousOn u T
  have hvariance :
      (∫ a in shortCutoff ε..shortEndpoint ε,
        shortShellDensity ε a * a ^ 2 *
          Real.cosh (u * a)) =
      -Vs := by
    change
      (∫ a in shortCutoff ε..shortEndpoint ε,
        shortShellDensity ε a * a ^ 2 *
          Real.cosh (u * a)) =
        -(∫ a in shortCutoff ε..shortEndpoint ε,
          (-shortShellDensity ε a) * a ^ 2 *
            Real.cosh ((1 + (u - 1)) * a))
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro a ha
    ring_nf
  have hpositivevariance :
      (∫ a in shellLocation ε..shellLocation ε + 1,
        positiveShellDensity ε a * a ^ 2 *
          Real.cosh (u * a)) =
      Vp := by
    change
      (∫ a in shellLocation ε..shellLocation ε + 1,
        positiveShellDensity ε a * a ^ 2 *
          Real.cosh (u * a)) =
      (∫ a in shellLocation ε..shellLocation ε + 1,
        positiveShellDensity ε a * a ^ 2 *
          Real.cosh ((1 + (u - 1)) * a))
    apply intervalIntegral.integral_congr
    intro a ha
    ring_nf
  have hhyperbolic :
      (realHyperbolicShellPhase ε u : ℂ) = Hs + Hp := by
    rw [← mellinShellPhase_imaginary]
    unfold mellinShellPhase
    try dsimp [Hs, Hp]
    congr 1
    · apply intervalIntegral.integral_congr
      intro a ha
      change
        (shortShellDensity ε a : ℂ) *
          (Complex.cos ((a : ℂ) *
            (Complex.I * (u : ℂ))) - 1) =
          (shortShellDensity ε a : ℂ) *
            ((Real.cosh (u * a) : ℂ) - 1)
      congr 1
      have harg :
          (a : ℂ) * (Complex.I * (u : ℂ)) =
            ((u * a : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [harg, Complex.cos_mul_I,
        ← Complex.ofReal_cosh]
    · apply intervalIntegral.integral_congr
      intro a ha
      change
        (positiveShellDensity ε a : ℂ) *
          (Complex.cos ((a : ℂ) *
            (Complex.I * (u : ℂ))) - 1) =
          (positiveShellDensity ε a : ℂ) *
            ((Real.cosh (u * a) : ℂ) - 1)
      congr 1
      have harg :
          (a : ℂ) * (Complex.I * (u : ℂ)) =
            ((u * a : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [harg, Complex.cos_mul_I,
        ← Complex.ofReal_cosh]
  have hs :
      (∫ a in shortCutoff ε..shortEndpoint ε,
        (shortShellDensity ε a : ℂ) *
          saddleSourceCosineQuadraticRemainder a u T) =
        Fs - Hs +
          Complex.I * ((T * Ls : ℝ) : ℂ) -
          ((T ^ 2 / 2 * Vs : ℝ) : ℂ) := by
    rw [hshort]
    change
      Fs - Hs + Complex.I * ((T * Ls : ℝ) : ℂ) +
          ((T ^ 2 / 2 *
            (∫ a in shortCutoff ε..shortEndpoint ε,
              shortShellDensity ε a * a ^ 2 *
                Real.cosh (u * a)) : ℝ) : ℂ) =
        Fs - Hs + Complex.I * ((T * Ls : ℝ) : ℂ) -
          ((T ^ 2 / 2 * Vs : ℝ) : ℂ)
    rw [hvariance]
    push_cast
    ring
  have hp :
      (∫ a in shellLocation ε..shellLocation ε + 1,
        (positiveShellDensity ε a : ℂ) *
          saddleSourceCosineQuadraticRemainder a u T) =
        Fp - Hp +
          Complex.I * ((T * Lp : ℝ) : ℂ) +
          ((T ^ 2 / 2 * Vp : ℝ) : ℂ) := by
    rw [hpositive]
    change
      Fp - Hp + Complex.I * ((T * Lp : ℝ) : ℂ) +
          ((T ^ 2 / 2 *
            (∫ a in shellLocation ε..shellLocation ε + 1,
              positiveShellDensity ε a * a ^ 2 *
                Real.cosh (u * a)) : ℝ) : ℂ) =
        Fp - Hp + Complex.I * ((T * Lp : ℝ) : ℂ) +
          ((T ^ 2 / 2 * Vp : ℝ) : ℂ)
    rw [hpositivevariance]
  unfold saddleSourceShellQuadraticRemainder
  rw [hs, hp, hhyperbolic]
  change
    (Fs - Hs + Complex.I * ((T * Ls : ℝ) : ℂ) -
        ((T ^ 2 / 2 * Vs : ℝ) : ℂ)) +
      (Fp - Hp + Complex.I * ((T * Lp : ℝ) : ℂ) +
        ((T ^ 2 / 2 * Vp : ℝ) : ℂ)) =
      (Fs + Fp) - (Hs + Hp) +
        Complex.I * ((T * (Ls + Lp) : ℝ) : ℂ) +
        ((T ^ 2 / 2 * (Vp - Vs) : ℝ) : ℂ)
  push_cast
  ring
end CohnElkies
