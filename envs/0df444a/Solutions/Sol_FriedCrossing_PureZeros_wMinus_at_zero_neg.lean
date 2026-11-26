-- Prove2me | solution 1 for FriedCrossing.PureZeros.wMinus_at_zero_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:47:30.057211+00:00
-- url     : https://prove2.me/submissions/91713b22-612f-444a-9959-37aa15d2e37f

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate
namespace FriedCrossing.PureZeros
theorem _root_.solution {a : ℝ} (ha : a < 0) : wMinus a 0 = a := by
  unfold wMinus disc
  have : Real.sqrt (a ^ 2) = -a := by rw [Real.sqrt_sq_eq_abs, abs_of_neg ha]
  rw [mul_zero, sub_zero, this]; ring
end FriedCrossing.PureZeros
