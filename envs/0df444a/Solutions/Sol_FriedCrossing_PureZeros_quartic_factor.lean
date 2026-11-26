-- Prove2me | solution 1 for FriedCrossing.PureZeros.quartic_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:58:30.737559+00:00
-- url     : https://prove2.me/submissions/fbc1f50b-72d1-4eb6-bfc5-4484b899ce68

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Theorems.Thm_FriedCrossing_PureZeros_quartic_div
import Theorems.Thm_FriedCrossing_PureZeros_rem_eq_zero

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate
namespace FriedCrossing.PureZeros
theorem _root_.solution {c₁ c₂ c₃ c₄ scl snc : ℝ} (hne : scl ≠ snc)
    (h1 : quartic c₁ c₂ c₃ c₄ scl = 0) (h2 : quartic c₁ c₂ c₃ c₄ snc = 0) (z : ℝ) :
    quartic c₁ c₂ c₃ c₄ z =
      (z - scl) * (z - snc) * (z ^ 2 - e₁of c₁ scl snc * z + e₂of c₁ c₂ scl snc) := by
  obtain ⟨hr1, hr0⟩ := rem_eq_zero hne h1 h2
  rw [quartic_div, hr1, hr0, zero_mul, sub_zero, add_zero]
end FriedCrossing.PureZeros
