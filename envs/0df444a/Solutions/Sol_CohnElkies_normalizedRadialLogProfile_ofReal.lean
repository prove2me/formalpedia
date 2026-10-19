-- Prove2me | solution 1 for CohnElkies.normalizedRadialLogProfile_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/7609a399-c205-40b9-b40a-3d3d526e691f

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_radialProfile_real

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hreal : IsRealValued f)
    (R v : ℝ) :
    (normalizedRadialLogProfile hd f R v : ℂ) =
      ((radialSurfaceArea d / radialL1Mass f : ℝ) : ℂ) *
        (((R * Real.exp v) ^ d : ℝ) : ℂ) *
        radialProfile hd f (R * Real.exp v) := by
  have hvalue :
      radialProfile hd f (R * Real.exp v) =
        (((radialProfile hd f (R * Real.exp v)).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using! radialProfile_real hd f hreal (R * Real.exp v)
  unfold normalizedRadialLogProfile
  rw [hvalue]
  simp only [Complex.ofReal_re]
  push_cast
  ring
end CohnElkies
