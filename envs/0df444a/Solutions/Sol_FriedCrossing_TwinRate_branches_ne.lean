-- Prove2me | solution 1 for FriedCrossing.TwinRate.branches_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:57:21.284339+00:00
-- url     : https://prove2.me/submissions/cfb38f02-2a4c-4e97-bce9-3dd6ce1f79a2

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07
import Theorems.Thm_FriedCrossing_TwinRate_wPlus_ne_wMinus

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.TwinRate
namespace FriedCrossing.TwinRate
theorem _root_.solution {sStar τ a b : ℝ} (hτ : τ ≠ 0) (h : 0 < disc a b) :
    sStar + τ * wPlus a b ≠ sStar + τ * wMinus a b := by
  intro heq
  have : τ * (wPlus a b - wMinus a b) = 0 := by linarith
  rcases mul_eq_zero.mp this with h0 | h0
  · exact hτ h0
  · exact wPlus_ne_wMinus h (sub_eq_zero.mp h0)
end FriedCrossing.TwinRate
