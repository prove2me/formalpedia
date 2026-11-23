-- Prove2me | solution 1 for Comp.add_ne_zero_iff_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:04:49.901242+00:00
-- url     : https://prove2.me/submissions/26c8fa0a-88e5-45e8-8e71-03836dda7ee9

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData

set_option autoImplicit true
open Comp
namespace Comp
theorem _root_.solution {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a + b ≠ 0 ↔ a ≠ 0 ∨ b ≠ 0 := by
  constructor
  · intro hab
    rcases eq_or_ne a 0 with ha0 | ha0
    · rcases eq_or_ne b 0 with hb0 | hb0
      · rw [ha0, hb0, add_zero] at hab
        exact absurd rfl hab
      · exact Or.inr hb0
    · exact Or.inl ha0
  · rintro (h | h)
    · intro hab
      have hpos : 0 < a := lt_of_le_of_ne ha (Ne.symm h)
      linarith
    · intro hab
      have hpos : 0 < b := lt_of_le_of_ne hb (Ne.symm h)
      linarith
end Comp
