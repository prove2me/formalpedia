-- Prove2me | solution 1 for CohnElkies.saddleSourceShortShellQuadraticRemainder_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/10e71ccf-e3ee-4fbb-bb01-8dfdaed49cc0

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_shortShellDensity_continuousOn_support
import Theorems.Thm_CohnElkies_saddleSourceWeightedCosineQuadraticRemainder_norm_le

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
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε),
      0 ≤ shortMargin ε a)
    (u T : ℝ) :
    ‖∫ a in shortCutoff ε..shortEndpoint ε,
        (shortShellDensity ε a : ℂ) *
          saddleSourceCosineQuadraticRemainder a u T‖ ≤
      (|T| ^ 3 / 6) *
        upperShortShellThirdMoment ε (u - 1) := by
  have ha₀ : 0 ≤ shortCutoff ε := by
    unfold shortCutoff
    positivity
  have hnegative :
      ContinuousOn (fun a : ℝ => -shortShellDensity ε a)
        (Icc (shortCutoff ε) (shortEndpoint ε)) :=
    (shortShellDensity_continuousOn_support hε).neg
  have hnonnegative (a : ℝ)
      (ha : a ∈ Icc (shortCutoff ε) (shortEndpoint ε)) :
      0 ≤ -shortShellDensity ε a := by
    have hapos : 0 < a := by
      have : 0 < shortCutoff ε := by
        unfold shortCutoff
        positivity
      exact this.trans_le ha.1
    unfold shortShellDensity
    have hm : 0 ≤ shortMargin ε a := hmargin a ha
    have hd : 0 < 2 * a ^ 2 * Real.cosh a := by
      positivity
    simpa using!
      div_nonneg
        (mul_nonneg hm (Real.exp_pos _).le)
        hd.le
  have hbound :=
    saddleSourceWeightedCosineQuadraticRemainder_norm_le
      (fun a : ℝ => -shortShellDensity ε a)
      horder ha₀ hnegative hnonnegative u T
  have hnorm :
      ‖∫ a in shortCutoff ε..shortEndpoint ε,
          (shortShellDensity ε a : ℂ) *
            saddleSourceCosineQuadraticRemainder a u T‖ =
      ‖∫ a in shortCutoff ε..shortEndpoint ε,
          ((-shortShellDensity ε a : ℝ) : ℂ) *
            saddleSourceCosineQuadraticRemainder a u T‖ := by
    have heq :
        (∫ a in shortCutoff ε..shortEndpoint ε,
          ((-shortShellDensity ε a : ℝ) : ℂ) *
            saddleSourceCosineQuadraticRemainder a u T) =
        -(∫ a in shortCutoff ε..shortEndpoint ε,
          (shortShellDensity ε a : ℂ) *
            saddleSourceCosineQuadraticRemainder a u T) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro a ha
      push_cast
      ring
    rw [heq, norm_neg]
  rw [hnorm]
  convert! hbound using 1
  unfold upperShortShellThirdMoment
  congr 1
  apply intervalIntegral.integral_congr
  intro a ha
  ring_nf
end CohnElkies
