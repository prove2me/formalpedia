-- Prove2me | solution 1 for CohnElkies.norm_integerGammaFactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/1220f136-84f8-413f-8332-338493813760

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
    ‖(j : ℂ) + Complex.I * (y : ℂ) / 2‖ =
      Real.sqrt ((j : ℝ) ^ 2 + (y / 2) ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp
  ring
end CohnElkies
