-- Prove2me | solution 1 for CohnElkies.realHyperbolicShellPhase_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/bbf23335-f8d7-4693-b1a1-b7538f5a746a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_realHyperbolicShellInterval_hasDerivAt

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (u : ℝ) :
    HasDerivAt (realHyperbolicShellPhase ε)
      ((∫ a in shortCutoff ε..shortEndpoint ε,
          shortShellDensity ε a * a * Real.sinh (a * u)) +
       (∫ a in shellLocation ε..shellLocation ε + 1,
          positiveShellDensity ε a * a * Real.sinh (a * u))) u := by
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
    exact (hn.div hd (fun a => by positivity [hmax a])).neg
  have hshortfun :
      (fun v : ℝ => ∫ a in shortCutoff ε..shortEndpoint ε,
        shortShellDensity ε a *
          (Real.cosh (a * v) - 1)) =
      (fun v : ℝ => ∫ a in shortCutoff ε..shortEndpoint ε,
        w a * (Real.cosh (a * v) - 1)) := by
    funext v
    apply intervalIntegral.integral_congr
    intro a ha
    rw [uIcc_of_le horder] at ha
    try dsimp [w]
    rw [max_eq_left ha.1]
  have hshortderiv :
      (∫ a in shortCutoff ε..shortEndpoint ε,
        shortShellDensity ε a * a * Real.sinh (a * u)) =
      (∫ a in shortCutoff ε..shortEndpoint ε,
        w a * a * Real.sinh (a * u)) := by
    apply intervalIntegral.integral_congr
    intro a ha
    rw [uIcc_of_le horder] at ha
    try dsimp [w]
    rw [max_eq_left ha.1]
  have hshort :
      HasDerivAt
        (fun v : ℝ => ∫ a in shortCutoff ε..shortEndpoint ε,
          shortShellDensity ε a *
            (Real.cosh (a * v) - 1))
        (∫ a in shortCutoff ε..shortEndpoint ε,
          shortShellDensity ε a * a * Real.sinh (a * u)) u := by
    rw [hshortfun, hshortderiv]
    exact realHyperbolicShellInterval_hasDerivAt
      w hw horder u
  have hremote : shellLocation ε ≤ shellLocation ε + 1 := by
    linarith
  have hpositive := realHyperbolicShellInterval_hasDerivAt
    (positiveShellDensity ε)
    (positiveShellDensity_continuous ε) hremote u
  exact hshort.add hpositive
end CohnElkies
