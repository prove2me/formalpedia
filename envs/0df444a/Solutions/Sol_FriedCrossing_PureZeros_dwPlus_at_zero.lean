-- Prove2me | solution 1 for FriedCrossing.PureZeros.dwPlus_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:58:19.673386+00:00
-- url     : https://prove2.me/submissions/4929b3fd-ea74-4d18-8a02-bff6124d8033

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate
namespace FriedCrossing.PureZeros
theorem _root_.solution {a a' b' : ℝ} (ha : a < 0) : dwPlus a 0 a' b' = b' / a := by
  have ha0 : a ≠ 0 := ha.ne
  unfold dwPlus disc
  have : Real.sqrt (a ^ 2) = -a := by rw [Real.sqrt_sq_eq_abs, abs_of_neg ha]
  rw [mul_zero, sub_zero, this]
  field_simp
  ring
end FriedCrossing.PureZeros
