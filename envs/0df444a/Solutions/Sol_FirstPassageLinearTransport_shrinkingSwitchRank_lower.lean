-- Prove2me | solution 1 for FirstPassageLinearTransport.shrinkingSwitchRank_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:14:13.307806+00:00
-- url     : https://prove2.me/submissions/284c4322-dfaf-4149-a878-832c54bf2e2b

import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (C : ℝ) (M : ℕ) :
    C * Real.log ((M : ℝ) + 2) ≤ (shrinkingSwitchRank C M : ℝ) :=
  Nat.le_ceil _
end FirstPassageLinearTransport
