-- Prove2me | solution 1 for CohnElkies.norm_halfIntegerGammaFactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/1f894a4a-a287-415f-842d-9df042b3a16f

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution (j : ℕ) (y : ℝ) :
    ‖(j : ℂ) + (1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2‖ =
      Real.sqrt (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp
  ring
end CohnElkies
