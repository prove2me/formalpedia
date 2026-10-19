-- Prove2me | solution 1 for CohnElkies.mellinShellPhase_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/abb2b412-6eb0-49b1-801b-78d67ac6235f

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_complexShellInterval_continuous

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    Continuous (mellinShellPhase ε) := by
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
  have hshort : Continuous (fun z : ℂ =>
      ∫ a in shortCutoff ε..shortEndpoint ε,
        (shortShellDensity ε a : ℂ) *
          (Complex.cos ((a : ℂ) * z) - 1)) := by
    apply (complexShellInterval_continuous w hw horder).congr
    intro z
    apply intervalIntegral.integral_congr
    intro a ha
    rw [uIcc_of_le horder] at ha
    try dsimp [w]
    rw [max_eq_left ha.1]
  have hremote : shellLocation ε ≤ shellLocation ε + 1 := by
    linarith
  have hpositive : Continuous (fun z : ℂ =>
      ∫ a in shellLocation ε..shellLocation ε + 1,
        (positiveShellDensity ε a : ℂ) *
          (Complex.cos ((a : ℂ) * z) - 1)) :=
    complexShellInterval_continuous (positiveShellDensity ε)
      (positiveShellDensity_continuous ε) hremote
  exact hshort.add hpositive
end CohnElkies
