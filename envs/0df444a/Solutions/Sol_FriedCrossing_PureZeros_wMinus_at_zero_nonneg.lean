-- Prove2me | solution 1 for FriedCrossing.PureZeros.wMinus_at_zero_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:58:27.940188+00:00
-- url     : https://prove2.me/submissions/9bab23b8-f367-4046-8ff2-3dd14f03da2e

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate
namespace FriedCrossing.PureZeros
theorem _root_.solution {a : ℝ} (ha : 0 ≤ a) : wMinus a 0 = 0 := by
  unfold wMinus disc
  rw [mul_zero, sub_zero, Real.sqrt_sq ha]; ring
end FriedCrossing.PureZeros
