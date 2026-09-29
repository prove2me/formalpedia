-- Prove2me | solution 1 for DiazModulus.diaz_of_exp_real
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T04:09:06.343976+00:00
-- url     : https://prove2.me/submissions/bad5d3a4-4bcd-4c55-b719-f5d60f75151a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_DiazModulus_diaz_of_exp_real_self_real
import Theorems.Thm_DiazModulus_diaz_of_exp_real_self_not_real

open Complex ComplexConjugate

open DiazModulus in
theorem solution :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im = 0 →
      Transcendental ℚ (Complex.exp u) := by
  intro u hu hmod hexpim
  by_cases h : u.im = 0
  · exact diaz_of_exp_real_self_real u hu hmod hexpim h
  · exact diaz_of_exp_real_self_not_real u hu hmod hexpim h
