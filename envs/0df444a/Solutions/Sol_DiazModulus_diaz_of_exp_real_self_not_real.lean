-- Prove2me | solution 1 for DiazModulus.diaz_of_exp_real_self_not_real
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T04:27:50.012013+00:00
-- url     : https://prove2.me/submissions/4f3ae977-678a-4b66-9e7e-149fd61ad7a2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_DiazModulus_diaz_of_exp_eq_one
import Theorems.Thm_DiazModulus_diaz_of_exp_ne_one

open Complex ComplexConjugate

open DiazModulus in
theorem solution :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im = 0 →
      u.im ≠ 0 → Transcendental ℚ (Complex.exp u) := by
  intro u hu hmod hre him
  by_cases h : Complex.exp u = 1
  · exact diaz_of_exp_eq_one u hu hmod hre him h
  · exact diaz_of_exp_ne_one u hu hmod hre him h
