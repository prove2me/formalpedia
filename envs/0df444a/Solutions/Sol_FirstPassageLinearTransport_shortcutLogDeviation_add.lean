-- Prove2me | solution 1 for FirstPassageLinearTransport.shortcutLogDeviation_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:47:20.754574+00:00
-- url     : https://prove2.me/submissions/404e601b-1a50-4dcb-817c-1597cf9d83bb

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Theorems.Thm_FirstPassageLinearTransport_orbit_add


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (n k j : ℕ) :
    shortcutLogDeviation n (j + k) =
      shortcutLogDeviation n k + shortcutLogDeviation (orbit k n) j := by
  rw [shortcutLogDeviation, shortcutLogDeviation, shortcutLogDeviation,
    orbit_add]
  push_cast
  ring
end FirstPassageLinearTransport
