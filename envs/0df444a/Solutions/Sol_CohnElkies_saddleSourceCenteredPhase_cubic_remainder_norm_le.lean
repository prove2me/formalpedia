-- Prove2me | solution 1 for CohnElkies.saddleSourceCenteredPhase_cubic_remainder_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/879469f7-080f-4f77-8ae5-30ebe286a103

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceShellCenteredPhase_cubic_remainder_norm_le
import Theorems.Thm_CohnElkies_upperGammaCenteredPhase_cubic_remainder_norm_le

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
    {ε ℓ u : ℝ}
    (hε : 0 < ε)
    (hℓ : 0 < ℓ)
    (hu : -1 < u)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε),
      0 ≤ shortMargin ε a)
    (T : ℝ) :
    ‖saddleSourceCenteredPhase ε ℓ u T +
        ((ℓ * saddleSourceGaussianVariance ε ℓ u / 2 *
          T ^ 2 : ℝ) : ℂ)‖ ≤
      (ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
        |T| ^ 3 := by
  have hη : 0 < 1 + u := by linarith
  have hgamma :=
    upperGammaCenteredPhase_cubic_remainder_norm_le
      hℓ hη T
  have hshell :=
    saddleSourceShellCenteredPhase_cubic_remainder_norm_le
      hε hℓ.le horder hmargin u T
  have heq :
      saddleSourceCenteredPhase ε ℓ u T +
          ((ℓ * saddleSourceGaussianVariance ε ℓ u / 2 *
            T ^ 2 : ℝ) : ℂ) =
        (upperGammaCenteredPhase ℓ (1 + u) T +
          ((ℓ * upperGammaVariance ℓ (1 + u) / 2 *
            T ^ 2 : ℝ) : ℂ)) +
        (saddleSourceShellCenteredPhase ε ℓ u T +
          ((ℓ * upperNetShellVariance ε (u - 1) / 2 *
            T ^ 2 : ℝ) : ℂ)) := by
    unfold saddleSourceCenteredPhase
      saddleSourceGaussianVariance upperSaddleVariance
    have harg : 2 + (u - 1) = 1 + u := by ring
    rw [harg]
    push_cast
    ring
  rw [heq]
  calc
    ‖(upperGammaCenteredPhase ℓ (1 + u) T +
          ((ℓ * upperGammaVariance ℓ (1 + u) / 2 *
            T ^ 2 : ℝ) : ℂ)) +
        (saddleSourceShellCenteredPhase ε ℓ u T +
          ((ℓ * upperNetShellVariance ε (u - 1) / 2 *
            T ^ 2 : ℝ) : ℂ))‖ ≤
      ‖upperGammaCenteredPhase ℓ (1 + u) T +
          ((ℓ * upperGammaVariance ℓ (1 + u) / 2 *
            T ^ 2 : ℝ) : ℂ)‖ +
        ‖saddleSourceShellCenteredPhase ε ℓ u T +
          ((ℓ * upperNetShellVariance ε (u - 1) / 2 *
            T ^ 2 : ℝ) : ℂ)‖ :=
          norm_add_le _ _
    _ ≤ (ℓ * upperGammaThirdMoment ℓ (1 + u) / 6) *
          |T| ^ 3 +
        (ℓ * upperNetShellThirdMoment ε (u - 1) / 6) *
          |T| ^ 3 :=
          add_le_add hgamma hshell
    _ = (ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
        |T| ^ 3 := by
          unfold upperSaddleThirdMoment
          have harg : 2 + (u - 1) = 1 + u := by ring
          rw [harg]
          ring
end CohnElkies
