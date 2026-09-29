-- Prove2me | solution 1 for DiazModulus.diaz_of_exp_ne_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T04:42:50.096041+00:00
-- url     : https://prove2.me/submissions/6ebb58c1-07f0-403f-9adc-4cf7ab020ea2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_DiazModulus_diaz_of_exp_real_pure_imaginary
import Theorems.Thm_DiazModulus_diaz_of_exp_real_generic

open Complex ComplexConjugate

open DiazModulus in
theorem solution :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im = 0 →
      u.im ≠ 0 → Complex.exp u ≠ 1 → Transcendental ℚ (Complex.exp u) := by
  intro u hu hmod hre him h1
  by_cases h : u.re = 0
  · exact diaz_of_exp_real_pure_imaginary u hu hmod hre him h1 h
  · exact diaz_of_exp_real_generic u hu hmod hre him h1 h
