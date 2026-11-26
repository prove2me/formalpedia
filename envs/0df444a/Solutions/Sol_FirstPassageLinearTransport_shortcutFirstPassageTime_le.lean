-- Prove2me | solution 1 for FirstPassageLinearTransport.shortcutFirstPassageTime_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:28:38.964539+00:00
-- url     : https://prove2.me/submissions/159dece8-b59c-4294-9766-a8610a1b9a71

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {n k : ℕ} {z : ℝ} (hk : (orbit k n : ℝ) ≤ z) :
    shortcutFirstPassageTime n z ≤ k :=
  Nat.sInf_le hk
end FirstPassageLinearTransport
