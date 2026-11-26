-- Prove2me | solution 1 for FriedCrossing.PureZeros.wPlus_at_zero_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:47:22.8924+00:00
-- url     : https://prove2.me/submissions/b8c683ee-e2d7-41dc-b4ee-0285ed64ff90

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Theorems.Thm_FriedCrossing_TwinRate_wPlus_at_cddp


set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate
namespace FriedCrossing.PureZeros
theorem _root_.solution {a : ℝ} (ha : 0 < a) : wPlus a 0 = a := wPlus_at_cddp ha
end FriedCrossing.PureZeros
