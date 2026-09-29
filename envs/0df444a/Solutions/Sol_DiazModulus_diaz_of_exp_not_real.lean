-- Prove2me | solution 1 for DiazModulus.diaz_of_exp_not_real
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T04:52:02.411659+00:00
-- url     : https://prove2.me/submissions/eca98159-aba7-4088-957b-2cc76aaef918
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_DiazModulus_diaz_of_exp_not_real_on_axes
import Theorems.Thm_DiazModulus_diaz_of_exp_not_real_off_axes

open Complex ComplexConjugate

open DiazModulus in
theorem solution :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
      Transcendental ℚ (Complex.exp u) := by
  intro u hu hmod hne
  by_cases h : (u.im = 0 ∨ u.re = 0)
  · exact diaz_of_exp_not_real_on_axes u hu hmod hne h
  · exact diaz_of_exp_not_real_off_axes u hu hmod hne h
