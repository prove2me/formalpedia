-- Prove2me | solution 1 for FirstPassageLinearTransport.shrinkingSwitchRank_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:47:52.489589+00:00
-- url     : https://prove2.me/submissions/36edd3f4-7b2b-406d-ae6a-6c4f078222d2

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
    {C : ℝ} (hC : 0 < C) (M : ℕ) :
    0 < shrinkingSwitchRank C M := by
  apply Nat.ceil_pos.mpr
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hx : (1 : ℝ) < (M : ℝ) + 2 := by
    linarith
  exact mul_pos hC (Real.log_pos hx)
end FirstPassageLinearTransport
