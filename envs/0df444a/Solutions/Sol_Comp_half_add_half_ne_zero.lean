-- Prove2me | solution 1 for Comp.half_add_half_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:38:07.290174+00:00
-- url     : https://prove2.me/submissions/0b0f300c-dcec-4b99-bbec-72fd374288df

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_SafetyChainQ

set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
namespace Comp
theorem _root_.solution {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    1 / 2 * a + 1 / 2 * b ≠ 0 ↔ a ≠ 0 ∨ b ≠ 0 := by
  constructor
  · intro h
    rcases eq_or_ne a 0 with ha0 | ha0
    · rcases eq_or_ne b 0 with hb0 | hb0
      · rw [ha0, hb0] at h
        norm_num at h
      · exact Or.inr hb0
    · exact Or.inl ha0
  · rintro (h | h)
    · have hpos : 0 < a := lt_of_le_of_ne ha (Ne.symm h)
      intro hzero
      linarith
    · have hpos : 0 < b := lt_of_le_of_ne hb (Ne.symm h)
      intro hzero
      linarith
end Comp
