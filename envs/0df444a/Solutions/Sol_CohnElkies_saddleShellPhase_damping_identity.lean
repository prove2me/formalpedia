-- Prove2me | solution 1 for CohnElkies.saddleShellPhase_damping_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/2d3564d2-2136-489a-8c04-efe6a6d99382

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_shortShellDensity_continuousOn_support
import Theorems.Thm_CohnElkies_mellinShellPhase_shifted_re
import Theorems.Thm_CohnElkies_saddle_shellInterval_hyperbolic_sub_oscillatory

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
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (ℓ T u : ℝ) :
    ℓ *
      (realHyperbolicShellPhase ε u -
        (mellinShellPhase ε
          ((T : ℂ) + Complex.I * (u : ℂ))).re) =
      positiveShellDamping ε ℓ (u - 1) T -
        upperShortShellDamping ε ℓ (u - 1) T := by
  have hshort :=
    saddle_shellInterval_hyperbolic_sub_oscillatory
      (shortShellDensity ε) horder
      (shortShellDensity_continuousOn_support hε) T u
  have hpositive :=
    saddle_shellInterval_hyperbolic_sub_oscillatory
      (positiveShellDensity ε)
      (show shellLocation ε ≤ shellLocation ε + 1 by
        linarith)
      (positiveShellDensity_continuous ε).continuousOn T u
  rw [mellinShellPhase_shifted_re hε horder T u]
  unfold realHyperbolicShellPhase
    positiveShellDamping upperShortShellDamping
  have hu : 1 + (u - 1) = u := by ring
  simp only [hu]
  have hshortNormalized :
      (∫ a in shortCutoff ε..shortEndpoint ε,
        (-shortShellDensity ε a) *
          Real.cosh (u * a) *
            (1 - Real.cos (a * T))) =
        -(∫ a in shortCutoff ε..shortEndpoint ε,
          shortShellDensity ε a *
            Real.cosh (a * u) *
              (1 - Real.cos (a * T))) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro a ha
    change
      -shortShellDensity ε a * Real.cosh (u * a) *
          (1 - Real.cos (a * T)) =
        -(shortShellDensity ε a * Real.cosh (a * u) *
          (1 - Real.cos (a * T)))
    rw [mul_comm u a]
    ring
  have hpositiveNormalized :
      (∫ a in shellLocation ε..shellLocation ε + 1,
        positiveShellDensity ε a *
          Real.cosh (u * a) *
            (1 - Real.cos (a * T))) =
        ∫ a in shellLocation ε..shellLocation ε + 1,
          positiveShellDensity ε a *
            Real.cosh (a * u) *
              (1 - Real.cos (a * T)) := by
    apply intervalIntegral.integral_congr
    intro a ha
    change
      positiveShellDensity ε a * Real.cosh (u * a) *
          (1 - Real.cos (a * T)) =
        positiveShellDensity ε a * Real.cosh (a * u) *
          (1 - Real.cos (a * T))
    rw [mul_comm u a]
  rw [hshortNormalized, hpositiveNormalized]
  linear_combination ℓ * hshort + ℓ * hpositive
end CohnElkies
