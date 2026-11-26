-- Prove2me | solution 1 for FriedCrossing.PureZeros.rem_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:57:12.311692+00:00
-- url     : https://prove2.me/submissions/834738aa-7277-4d4c-9210-bd68a6e169bd

import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Theorems.Thm_FriedCrossing_PureZeros_quartic_div

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology
open FriedCrossing.PureZeros
open TwinRate
namespace FriedCrossing.PureZeros
theorem _root_.solution {c₁ c₂ c₃ c₄ scl snc : ℝ} (hne : scl ≠ snc)
    (h1 : quartic c₁ c₂ c₃ c₄ scl = 0) (h2 : quartic c₁ c₂ c₃ c₄ snc = 0) :
    rem₁ c₁ c₂ c₃ scl snc = 0 ∧ rem₀ c₁ c₂ c₄ scl snc = 0 := by
  have e1 := quartic_div c₁ c₂ c₃ c₄ scl snc scl
  have e2 := quartic_div c₁ c₂ c₃ c₄ scl snc snc
  rw [h1] at e1
  rw [h2] at e2
  have h3 : rem₁ c₁ c₂ c₃ scl snc * (scl - snc) = 0 := by linear_combination e1 - e2
  have hr1 : rem₁ c₁ c₂ c₃ scl snc = 0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hne
  refine ⟨hr1, ?_⟩
  linear_combination -e1 + scl * hr1
end FriedCrossing.PureZeros
