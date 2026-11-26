-- Prove2me | solution 1 for FriedCrossing.TwinRate.wPlus_mul_wMinus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:39:16.14857+00:00
-- url     : https://prove2.me/submissions/aa483b3e-efdf-4ce4-95c9-938f13e619d6

import Definitions.Def_B1s_fried_crossing_9_03
import Definitions.Def_B1s_fried_crossing_rate_9_07

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.TwinRate
namespace FriedCrossing.TwinRate
theorem _root_.solution {a b : ℝ} (h : 0 ≤ disc a b) : wPlus a b * wMinus a b = b := by
  unfold wPlus wMinus
  have := Real.sq_sqrt h
  unfold disc at this ⊢
  nlinarith [this]
end FriedCrossing.TwinRate
