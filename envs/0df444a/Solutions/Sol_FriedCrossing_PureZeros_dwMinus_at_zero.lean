-- Prove2me | solution 1 for FriedCrossing.PureZeros.dwMinus_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:58:14.412643+00:00
-- url     : https://prove2.me/submissions/22232d18-afd8-42bb-9721-0fb2b1d37051

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate
namespace FriedCrossing.PureZeros
theorem _root_.solution {a a' b' : ℝ} (ha : 0 < a) : dwMinus a 0 a' b' = b' / a := by
  have ha0 : a ≠ 0 := ha.ne'
  unfold dwMinus disc
  rw [mul_zero, sub_zero, Real.sqrt_sq ha.le]
  field_simp
  ring
end FriedCrossing.PureZeros
