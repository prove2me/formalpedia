-- Prove2me | solution 1 for CohnElkies.saddleSourceShellDerivative_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/b7b97af8-3931-4849-b1ce-f8951889a732

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSinhShellInterval_hasDerivAt

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (u : ℝ) :
    HasDerivAt (saddleSourceShellDerivative ε)
      (upperNetShellVariance ε (u - 1)) u := by
  have hcutoff : 0 < shortCutoff ε := by
    unfold shortCutoff
    positivity
  let w : ℝ → ℝ := fun a =>
    shortShellDensity ε (max a (shortCutoff ε))
  have hmax (a : ℝ) : 0 < max a (shortCutoff ε) :=
    hcutoff.trans_le (le_max_right _ _)
  have hw : Continuous w := by
    have hn : Continuous (fun a : ℝ =>
        shortMargin ε (max a (shortCutoff ε)) *
          Real.exp (-2 * max a (shortCutoff ε))) := by
      unfold shortMargin
      fun_prop
    have hd : Continuous (fun a : ℝ =>
        2 * (max a (shortCutoff ε)) ^ 2 *
          Real.cosh (max a (shortCutoff ε))) := by
      fun_prop
    try dsimp [w]
    unfold shortShellDensity
    exact (hn.div hd (fun a => by
      positivity [hmax a])).neg
  have hshort :
      HasDerivAt
        (fun v : ℝ =>
          ∫ a in shortCutoff ε..shortEndpoint ε,
            shortShellDensity ε a * a *
              Real.sinh (v * a))
        (∫ a in shortCutoff ε..shortEndpoint ε,
          shortShellDensity ε a * a ^ 2 *
            Real.cosh (u * a)) u := by
    have h := saddleSinhShellInterval_hasDerivAt
      w hw horder u
    convert! h using 1
    · funext v
      apply intervalIntegral.integral_congr
      intro a ha
      rw [uIcc_of_le horder] at ha
      try dsimp [w]
      rw [max_eq_left ha.1]
      congr 2
      ring
    · apply intervalIntegral.integral_congr
      intro a ha
      rw [uIcc_of_le horder] at ha
      try dsimp [w]
      rw [max_eq_left ha.1]
      congr 2
      ring
  have hremote : shellLocation ε ≤ shellLocation ε + 1 := by
    linarith
  have hpositive :
      HasDerivAt
        (fun v : ℝ =>
          ∫ a in shellLocation ε..shellLocation ε + 1,
            positiveShellDensity ε a * a *
              Real.sinh (v * a))
        (∫ a in shellLocation ε..shellLocation ε + 1,
          positiveShellDensity ε a * a ^ 2 *
            Real.cosh (u * a)) u := by
    have h := saddleSinhShellInterval_hasDerivAt
      (positiveShellDensity ε)
      (positiveShellDensity_continuous ε)
      hremote u
    convert! h using 1
    · funext v
      apply intervalIntegral.integral_congr
      intro a ha
      ring_nf
    · apply intervalIntegral.integral_congr
      intro a ha
      ring_nf
  have hshortvariance :
      (∫ a in shortCutoff ε..shortEndpoint ε,
        shortShellDensity ε a * a ^ 2 *
          Real.cosh (u * a)) =
        -upperShortShellVariance ε (u - 1) := by
    unfold upperShortShellVariance
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro a ha
    ring_nf
  have hpositivevariance :
      (∫ a in shellLocation ε..shellLocation ε + 1,
        positiveShellDensity ε a * a ^ 2 *
          Real.cosh (u * a)) =
        upperPositiveShellVariance ε (u - 1) := by
    unfold upperPositiveShellVariance
    apply intervalIntegral.integral_congr
    intro a ha
    ring_nf
  have hsum := hshort.add hpositive
  unfold saddleSourceShellDerivative
  convert! hsum using 1
  rw [hshortvariance, hpositivevariance]
  unfold upperNetShellVariance
  ring
end CohnElkies
