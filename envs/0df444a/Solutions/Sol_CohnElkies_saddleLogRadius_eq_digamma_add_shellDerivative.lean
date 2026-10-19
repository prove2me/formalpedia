-- Prove2me | solution 1 for CohnElkies.saddleLogRadius_eq_digamma_add_shellDerivative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/3706700f-ce0f-4fc0-927f-25d86f3cfce8

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
    (ε : ℝ) (d : ℕ) (u : ℝ) :
    saddleLogRadius ε d u =
      -(Real.log Real.pi) / 2 +
        saddleDigamma (((d : ℝ) / 2) * (1 + u) / 2) / 2 +
          saddleSourceShellDerivative ε u := by
  unfold saddleLogRadius saddleSourceShellDerivative
  ring
end CohnElkies
