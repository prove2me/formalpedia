-- Prove2me | solution 1 for FriedCrossing.PureZeros.quartic_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:46:25.174463+00:00
-- url     : https://prove2.me/submissions/b3b5f6fd-53aa-48f2-8b05-054b65433400

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate
namespace FriedCrossing.PureZeros
theorem _root_.solution (c₁ c₂ c₃ c₄ scl snc z : ℝ) :
    quartic c₁ c₂ c₃ c₄ z =
      (z - scl) * (z - snc) * (z ^ 2 - e₁of c₁ scl snc * z + e₂of c₁ c₂ scl snc)
        - rem₁ c₁ c₂ c₃ scl snc * z + rem₀ c₁ c₂ c₄ scl snc := by
  simp only [quartic, e₁of, e₂of, rem₁, rem₀]; ring
end FriedCrossing.PureZeros
