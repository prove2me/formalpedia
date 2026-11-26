-- Prove2me | solution 1 for FirstPassageLinearTransport.shortcutFirstPassageTime_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:47:52.802089+00:00
-- url     : https://prove2.me/submissions/5d93d981-69d6-4853-8b73-680477757913

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
    (orbit (shortcutFirstPassageTime n z) n : ℝ) ≤ z := by
  unfold shortcutFirstPassageTime
  exact Nat.sInf_mem
    (show {j : ℕ | (orbit j n : ℝ) ≤ z}.Nonempty from ⟨k, hk⟩)
end FirstPassageLinearTransport
