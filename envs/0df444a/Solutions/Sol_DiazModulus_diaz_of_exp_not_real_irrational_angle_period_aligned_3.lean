-- Prove2me | solution 3 for DiazModulus.diaz_of_exp_not_real_irrational_angle_period_aligned
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T07:55:36.219981+00:00
-- url     : https://prove2.me/submissions/74e7bc1b-2793-4f65-bb36-c52699ac75e3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_diaz_of_exp_not_real_irrational_angle_period_aligned_norm_rat_mult
import Theorems.Thm_DiazModulus_diaz_of_exp_not_real_irrational_angle_period_aligned_norm_free

open Complex ComplexConjugate

theorem _root_.solution :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
      ¬ (u.im = 0 ∨ u.re = 0) → (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) →
      (∃ r : ℚ, r ≠ 0 ∧
        IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) →
      Transcendental ℚ (Complex.exp u) := by
  intro u hu hnorm hre hax hang hal
  by_cases h : ∃ r : ℚ, r ≠ 0 ∧
      IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ) ∧
      ∃ c : ℚ, (‖u‖ : ℝ) ^ 2 = (c : ℝ) * (Real.pi * (u.im + (r : ℝ) * Real.pi))
  · exact DiazModulus.diaz_of_exp_not_real_irrational_angle_period_aligned_norm_rat_mult
      u hu hnorm hre hax hang hal h
  · exact DiazModulus.diaz_of_exp_not_real_irrational_angle_period_aligned_norm_free
      u hu hnorm hre hax hang hal h

#print axioms solution
