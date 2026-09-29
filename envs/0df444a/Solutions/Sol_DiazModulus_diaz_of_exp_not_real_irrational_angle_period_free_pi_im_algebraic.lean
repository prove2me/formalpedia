-- Prove2me | solution 1 for DiazModulus.diaz_of_exp_not_real_irrational_angle_period_free_pi_im_algebraic
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T14:24:49.597275+00:00
-- url     : https://prove2.me/submissions/c09daafc-b96b-403a-a313-f580fe075cf8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_recip_pi_not_log
import Theorems.Thm_DiazModulus_recip_pi_log_of_pi_im_algebraic

open Complex ComplexConjugate

-- The leaf is the composite of its own route lemma with (S).
-- Route: an irrational angle with `π · Im u` algebraic, on a logarithm of an algebraic
-- number, produces an algebraic `γ ≠ 0` with `exp (γ / (πi))` algebraic.
-- (S): no such `γ` exists. So `exp u` cannot be algebraic.
-- None of `u ≠ 0`, `‖u‖ ∈ Q̄`, `(exp u).im ≠ 0`, the off-axes clause, or the period-free
-- clause is used: the leaf holds on a strictly larger set than it is stated on.

open DiazModulus in
theorem solution :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
      ¬ (u.im = 0 ∨ u.re = 0) → (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) →
      (¬ ∃ r : ℚ, r ≠ 0 ∧
        IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) →
      IsAlgebraic ℚ ((Real.pi * u.im : ℝ) : ℂ) →
      Transcendental ℚ (Complex.exp u) := by
  intro u _hu0 _hmod _him _hoff hirr _hfree hpa hexp
  obtain ⟨γ, hγalg, hγ0, hγexp⟩ :=
    DiazModulus.recip_pi_log_of_pi_im_algebraic u hirr hpa hexp
  exact DiazModulus.recip_pi_not_log γ hγalg hγ0 hγexp
