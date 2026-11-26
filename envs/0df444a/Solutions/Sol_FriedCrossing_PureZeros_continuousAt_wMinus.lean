-- Prove2me | solution 1 for FriedCrossing.PureZeros.continuousAt_wMinus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:47:01.607702+00:00
-- url     : https://prove2.me/submissions/c2ca0d8c-4cfc-4671-9319-5d5b056b7ad0

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate
namespace FriedCrossing.PureZeros
theorem _root_.solution (p : ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ => wMinus q.1 q.2) p := by
  unfold wMinus disc
  fun_prop
end FriedCrossing.PureZeros
