-- Prove2me | solution 1 for Eden.one_radius_zero_of_evolution_return
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:19:22.975934+00:00
-- url     : https://prove2.me/submissions/6175806d-3fe9-4056-99a4-b739592dd360

import Definitions.Def_Eden_RadialReturns
import Mathlib.NumberTheory.Real.Irrational
import Definitions.Def_Eden_RotationReturns
import Theorems.Thm_Eden_not_simultaneous_rotation_returns
import Theorems.Thm_Eden_first_cos_eq_one_of_evolution_return
import Theorems.Thm_Eden_second_cos_eq_one_of_evolution_return

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (h : evolution c t p = p) : radiusSq₁ p = 0 ∨ radiusSq₂ p = 0 := by
  by_cases h₁ : radiusSq₁ p = 0
  · exact Or.inl h₁
  by_cases h₂ : radiusSq₂ p = 0
  · exact Or.inr h₂
  exact False.elim (not_simultaneous_rotation_returns ht
    ⟨first_cos_eq_one_of_evolution_return c ht h₁ h,
      second_cos_eq_one_of_evolution_return c ht h₂ h⟩)
end Eden
