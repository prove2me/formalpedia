-- Prove2me | solution 1 for FirstPassageLinearTransport.shrinkingSwitchRank_lt_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:13:34.51038+00:00
-- url     : https://prove2.me/submissions/d881f2be-125c-42b0-9566-6f18631cb942

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
theorem _root_.solution
    {C : ℝ} (hC : 0 ≤ C) (M : ℕ) :
    (shrinkingSwitchRank C M : ℝ) <
      C * Real.log ((M : ℝ) + 2) + 1 := by
  apply Nat.ceil_lt_add_one
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hx : (1 : ℝ) ≤ (M : ℝ) + 2 := by
    linarith
  exact mul_nonneg hC (Real.log_nonneg hx)
end FirstPassageLinearTransport
