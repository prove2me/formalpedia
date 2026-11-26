-- Prove2me | solution 1 for FirstPassageLinearTransport.rawOrbit_rawTime_add_one_eq_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:47:40.845929+00:00
-- url     : https://prove2.me/submissions/03a1d028-d3e1-436d-ae5f-6af5bcdcfe2b

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Theorems.Thm_FirstPassageLinearTransport_orbit_succ
import Theorems.Thm_FirstPassageLinearTransport_rawCollatz_of_odd
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_add
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_rawTime_eq_orbit
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_succ
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {n j : ℕ} (hodd : orbit j n % 2 = 1) :
    rawOrbit (rawTime n j + 1) n = 2 * orbit (j + 1) n := by
  rw [show rawTime n j + 1 = 1 + rawTime n j by omega,
    rawOrbit_add, rawOrbit_rawTime_eq_orbit,
    rawOrbit_succ, rawOrbit_zero, rawCollatz_of_odd hodd,
    orbit_succ]
  exact (two_mul_shortcut_of_odd hodd).symm
end FirstPassageLinearTransport
