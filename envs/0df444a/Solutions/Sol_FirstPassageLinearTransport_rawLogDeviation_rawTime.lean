-- Prove2me | solution 1 for FirstPassageLinearTransport.rawLogDeviation_rawTime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:19:08.87672+00:00
-- url     : https://prove2.me/submissions/4f78e61f-aa40-434c-95bc-1a35e74f34a8

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_rawTime_eq_orbit


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (n j : ℕ) :
    rawLogDeviation n (rawTime n j) =
      shortcutLogDeviation n j + rawOddDeviationCoefficient *
        ((oddCount n j : ℝ) - (j : ℝ) / 2) := by
  rw [rawLogDeviation, rawOrbit_rawTime_eq_orbit, rawTime,
    shortcutLogDeviation, rawOddDeviationCoefficient]
  push_cast
  ring
end FirstPassageLinearTransport
