-- Prove2me | solution 1 for CohnElkies.saddleSourceMellinContour_gammaArgument
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/5568c3d4-1b18-435f-8dcb-2f765a6643fb

import Mathlib
import Definitions.Def_SpherePacking

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
    (ℓ u T : ℝ) :
    saddleSourceMellinContour ℓ u T / 2 =
      ((ℓ * (1 + u) / 2 : ℝ) : ℂ) -
        Complex.I * ((ℓ * T / 2 : ℝ) : ℂ) := by
  unfold saddleSourceMellinContour
  push_cast
  ring
end CohnElkies
