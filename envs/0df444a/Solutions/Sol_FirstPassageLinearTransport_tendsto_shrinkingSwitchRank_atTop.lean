-- Prove2me | solution 1 for FirstPassageLinearTransport.tendsto_shrinkingSwitchRank_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:48:30.608525+00:00
-- url     : https://prove2.me/submissions/59f25d46-32da-41e1-8d65-20e15ec2d002

import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Theorems.Thm_FirstPassageLinearTransport_shrinkingSwitchRank_lower

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {C : ℝ} (hC : 0 < C) :
    Tendsto (shrinkingSwitchRank C) atTop atTop := by
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ)
      tendsto_natCast_atTop_atTop
  have hlogT : Tendsto (fun M : ℕ => Real.log ((M : ℝ) + 2))
      atTop atTop := Real.tendsto_log_atTop.comp hxT
  have hreal : Tendsto
      (fun M : ℕ => C * Real.log ((M : ℝ) + 2)) atTop atTop :=
    hlogT.const_mul_atTop hC
  rw [tendsto_atTop]
  intro N
  have hN := (tendsto_atTop.1 hreal) (N : ℝ)
  filter_upwards [hN] with M hN
  exact_mod_cast hN.trans (shrinkingSwitchRank_lower C M)
end FirstPassageLinearTransport
