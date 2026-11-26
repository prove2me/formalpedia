-- Prove2me | solution 1 for FriedCrossing.PureZeros.quartic_roots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:11:19.406896+00:00
-- url     : https://prove2.me/submissions/0c0621f5-8077-49f3-a357-128d01b7d8a1

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Theorems.Thm_FriedCrossing_PureZeros_quartic_factor

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate
namespace FriedCrossing.PureZeros
theorem _root_.solution {c₁ c₂ c₃ c₄ scl snc : ℝ} (hne : scl ≠ snc)
    (h1 : quartic c₁ c₂ c₃ c₄ scl = 0) (h2 : quartic c₁ c₂ c₃ c₄ snc = 0) (z : ℝ) :
    quartic c₁ c₂ c₃ c₄ z = 0 ↔
      z = scl ∨ z = snc ∨ z ^ 2 - e₁of c₁ scl snc * z + e₂of c₁ c₂ scl snc = 0 := by
  rw [quartic_factor hne h1 h2, mul_eq_zero, mul_eq_zero, sub_eq_zero, sub_eq_zero, or_assoc]
end FriedCrossing.PureZeros
