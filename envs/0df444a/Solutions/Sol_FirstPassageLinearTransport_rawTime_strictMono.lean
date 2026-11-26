-- Prove2me | solution 1 for FirstPassageLinearTransport.rawTime_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:19:52.049285+00:00
-- url     : https://prove2.me/submissions/3d405f71-a5d5-4856-8589-1200ed6c737f

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Theorems.Thm_FirstPassageLinearTransport_oddCount_mono


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (n : ℕ) : StrictMono (rawTime n) := by
  intro a b hab
  have hodd := oddCount_mono (n := n) hab.le
  unfold rawTime
  omega
end FirstPassageLinearTransport
