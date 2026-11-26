-- Prove2me | solution 1 for FriedCrossing.TwinRate.wPlus_ne_wMinus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:56:02.958652+00:00
-- url     : https://prove2.me/submissions/f9144c2f-bb93-480c-8ad9-8b3539b0473d

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07
import Theorems.Thm_FriedCrossing_TwinRate_wPlus_sub_wMinus

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.TwinRate
namespace FriedCrossing.TwinRate
theorem _root_.solution {a b : ℝ} (h : 0 < disc a b) : wPlus a b ≠ wMinus a b := by
  intro heq
  have := wPlus_sub_wMinus a b
  rw [heq, sub_self] at this
  exact (Real.sqrt_pos.mpr h).ne this
end FriedCrossing.TwinRate
