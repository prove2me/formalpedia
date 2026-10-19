-- Prove2me | solution 2 for CohnElkies.saddleLogRadius_eq_digamma_add_shellDerivative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:10:27.749063+00:00
-- url     : https://prove2.me/submissions/c7bc5c10-ec8c-477e-91b3-50e98be6a586

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


theorem solution
    (ε : ℝ) (d : ℕ) (u : ℝ) :
    saddleLogRadius ε d u =
      -(Real.log Real.pi) / 2 +
        saddleDigamma (((d : ℝ) / 2) * (1 + u) / 2) / 2 +
          saddleSourceShellDerivative ε u := by
  unfold saddleLogRadius saddleSourceShellDerivative
  ring

