-- Prove2me | solution 1 for FirstPassageLinearTransport.rawFirstPassageTime_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:21:52.079798+00:00
-- url     : https://prove2.me/submissions/72f87621-f388-4964-9ce3-9a851d37c6f5

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
    (rawOrbit (rawFirstPassageTime n z) n : ℝ) ≤ z := by
  unfold rawFirstPassageTime
  exact Nat.sInf_mem
    (show {i : ℕ | (rawOrbit i n : ℝ) ≤ z}.Nonempty from ⟨i, hi⟩)
end FirstPassageLinearTransport
