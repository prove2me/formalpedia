-- Prove2me | solution 1 for DiazModulus.diaz_of_exp_not_real_irrational_angle_period_aligned_norm_free
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T20:23:45.438484+00:00
-- url     : https://prove2.me/submissions/9e630e2d-99a6-42db-928f-bbbf8d048e0c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_recip_pi_log_of_period_aligned
import Theorems.Thm_DiazModulus_recip_pi_not_log

open Complex ComplexConjugate

-- The norm-free half is not an independent difficulty. Its distinguishing hypothesis --
-- that the square of the modulus is NOT a rational multiple of the aligned datum -- is
-- carried and never used. The proof is the period-aligned route lemma composed with (S):
-- the route produces an algebraic gamma /= 0 with exp(gamma/(i*pi)) algebraic, and (S) says
-- no such gamma exists. Everything else in the statement goes unused too.

open DiazModulus in
theorem solution :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
      ¬ (u.im = 0 ∨ u.re = 0) → (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) →
      (∃ r : ℚ, r ≠ 0 ∧
        IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) →
      (¬ ∃ r : ℚ, r ≠ 0 ∧
        IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ) ∧
        ∃ c : ℚ, (‖u‖ : ℝ) ^ 2 = (c : ℝ) * (Real.pi * (u.im + (r : ℝ) * Real.pi))) →
      Transcendental ℚ (Complex.exp u) := by
  intro u _hu _hnorm _him _hoff htheta haligned _hfree
  show ¬ IsAlgebraic ℚ (Complex.exp u)
  by_contra hcon
  obtain ⟨γ, hγ, hγ0, hγexp⟩ :=
    DiazModulus.recip_pi_log_of_period_aligned u htheta haligned hcon
  exact (DiazModulus.recip_pi_not_log γ hγ hγ0) hγexp
