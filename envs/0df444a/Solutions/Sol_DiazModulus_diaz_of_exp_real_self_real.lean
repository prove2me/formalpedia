-- Prove2me | solution 1 for DiazModulus.diaz_of_exp_real_self_real
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T04:11:02.719788+00:00
-- url     : https://prove2.me/submissions/63f2aa38-b36a-47c9-80c3-43323240013d

import Theorems.Thm_DiazModulus_diaz_on_axes_of_hermite_lindemann
import Theorems.Thm_DiazModulus_hermite_lindemann_holds

open Complex ComplexConjugate

open DiazModulus in
theorem solution :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im = 0 →
      u.im = 0 → Transcendental ℚ (Complex.exp u) := by
  intro u hu hmod _ him
  exact diaz_on_axes_of_hermite_lindemann hermite_lindemann_holds u hu (Or.inl him) hmod
