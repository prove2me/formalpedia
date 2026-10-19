-- Prove2me | solution 1 for CohnElkies.radialProfile_smooth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/216e1f75-3cc8-4554-ae3e-a8dcbe2871be

import Mathlib
import Definitions.Def_SpherePacking

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
    (hd : 0 < d) (f : TestFunction d) (n : ℕ∞) :
    ContDiff ℝ n (radialProfile hd f) := by
  simpa using! (radialSchwartzProfile hd f).smooth n
end CohnElkies
