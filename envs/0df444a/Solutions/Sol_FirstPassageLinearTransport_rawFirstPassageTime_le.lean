-- Prove2me | solution 1 for FirstPassageLinearTransport.rawFirstPassageTime_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:47:58.617262+00:00
-- url     : https://prove2.me/submissions/c9cbea18-e4fa-4735-bf6f-bcfd1b28e639

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {n i : ℕ} {z : ℝ} (hi : (rawOrbit i n : ℝ) ≤ z) :
    rawFirstPassageTime n z ≤ i :=
  Nat.sInf_le hi
end FirstPassageLinearTransport
