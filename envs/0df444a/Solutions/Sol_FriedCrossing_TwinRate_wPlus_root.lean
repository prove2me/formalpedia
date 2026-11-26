-- Prove2me | solution 1 for FriedCrossing.TwinRate.wPlus_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:54:49.16761+00:00
-- url     : https://prove2.me/submissions/90f10fee-47e2-4e8f-a580-bd22f67e120e

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07
import Theorems.Thm_FriedCrossing_TwinRate_wPlus_add_wMinus
import Theorems.Thm_FriedCrossing_TwinRate_wPlus_mul_wMinus

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.TwinRate
namespace FriedCrossing.TwinRate
theorem _root_.solution {a b : ℝ} (h : 0 ≤ disc a b) :
    wPlus a b ^ 2 - a * wPlus a b + b = 0 := by
  have h1 := wPlus_add_wMinus a b
  have h2 := wPlus_mul_wMinus h
  have : wPlus a b ^ 2 - a * wPlus a b + b =
      wPlus a b ^ 2 - (wPlus a b + wMinus a b) * wPlus a b + wPlus a b * wMinus a b := by
    rw [h1, h2]
  rw [this]; ring
end FriedCrossing.TwinRate
