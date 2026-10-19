-- Prove2me | solution 1 for CohnElkies.normalizedRadialLogProfile_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/02d64948-d7d0-4876-8f55-53530c524024

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_radialLogRadius_pow

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology ENNReal
namespace CohnElkies
theorem _root_.solution {d : ℕ} (hd : 0 < d)
    (g : TestFunction d) (R v : ℝ) :
    normalizedRadialLogProfile hd g R v =
      (radialSurfaceArea d / radialL1Mass g) *
        ((R * Real.exp v) *
          ((R * Real.exp v) ^ (d - 1) *
            (radialProfile hd g (R * Real.exp v)).re)) := by
  unfold normalizedRadialLogProfile
  rw [radialLogRadius_pow hd]
  ring
end CohnElkies
