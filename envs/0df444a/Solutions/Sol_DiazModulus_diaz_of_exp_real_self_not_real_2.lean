-- Prove2me | solution 2 for DiazModulus.diaz_of_exp_real_self_not_real
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T07:34:48.537496+00:00
-- url     : https://prove2.me/submissions/a2dedf60-30e7-4b29-8e04-66db9e63873c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_diaz_of_exp_eq_one
import Theorems.Thm_DiazModulus_diaz_of_exp_ne_one

open Complex ComplexConjugate



theorem _root_.solution :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im = 0 →
      u.im ≠ 0 → Transcendental ℚ (Complex.exp u) := by
  intro u hu hnorm hre him
  by_cases h : Complex.exp u = 1
  · exact DiazModulus.diaz_of_exp_eq_one u hu hnorm hre him h
  · exact DiazModulus.diaz_of_exp_ne_one u hu hnorm hre him h

#print axioms solution
