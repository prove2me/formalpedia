-- Prove2me | solution 1 for DiazModulus.diaz_of_exp_not_real_on_axes
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T04:53:35.471406+00:00
-- url     : https://prove2.me/submissions/809f9205-66db-4f13-ab08-a1b22d0ace79

import Theorems.Thm_DiazModulus_diaz_on_axes_of_hermite_lindemann
import Theorems.Thm_DiazModulus_hermite_lindemann_holds

open Complex ComplexConjugate

open DiazModulus in
theorem solution :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
      (u.im = 0 ∨ u.re = 0) → Transcendental ℚ (Complex.exp u) := by
  intro u hu hmod _ hax
  exact diaz_on_axes_of_hermite_lindemann hermite_lindemann_holds u hu hax hmod
