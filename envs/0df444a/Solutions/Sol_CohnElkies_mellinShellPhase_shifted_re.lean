-- Prove2me | solution 1 for CohnElkies.mellinShellPhase_shifted_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/34451d8d-0a26-46ae-9213-9c9cbbb3d22a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddle_complexShellInterval_re
import Theorems.Thm_CohnElkies_shortShellDensity_continuousOn_support

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
    (T u : ℝ) :
    (mellinShellPhase ε
      ((T : ℂ) + Complex.I * (u : ℂ))).re =
      (∫ a in shortCutoff ε..shortEndpoint ε,
        shortShellDensity ε a *
          (Real.cos (a * T) * Real.cosh (a * u) - 1)) +
      (∫ a in shellLocation ε..shellLocation ε + 1,
        positiveShellDensity ε a *
          (Real.cos (a * T) * Real.cosh (a * u) - 1)) := by
  unfold mellinShellPhase
  rw [Complex.add_re]
  congr 1
  · exact saddle_complexShellInterval_re
      (shortShellDensity ε) horder
      (shortShellDensity_continuousOn_support hε) T u
  · exact saddle_complexShellInterval_re
      (positiveShellDensity ε)
      (show shellLocation ε ≤ shellLocation ε + 1 by
        linarith)
      (positiveShellDensity_continuous ε).continuousOn T u
end CohnElkies
