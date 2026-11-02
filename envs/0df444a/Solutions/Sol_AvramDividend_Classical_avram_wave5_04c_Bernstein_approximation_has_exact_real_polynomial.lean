-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_Bernstein_approximation_has_exact_real_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:47:46.967379+00:00
-- url     : https://prove2.me/submissions/17ec1247-83cc-4c71-8b7a-9fd1fbef4e64

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Set Filter
open scoped BigOperators

/-! An explicit real polynomial realising every finite Bernstein approximation. -/
theorem solution (n : ℕ) (f : C(unitInterval.Elem, ℝ)) :
    ∃ p : Polynomial ℝ, ∀ t : unitInterval.Elem,
      Polynomial.eval (t : ℝ) p = (bernsteinApproximation n f) t := by
  let p : Polynomial ℝ :=
    ∑ k : Fin (n + 1),
      Polynomial.C (((Nat.choose n k.val : ℕ) : ℝ) * f (bernstein.z k)) *
        Polynomial.X ^ k.val * (1 - Polynomial.X) ^ (n - k.val)
  refine ⟨p, ?_⟩
  intro t
  rw [bernsteinApproximation.apply]
  simp only [p, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_sub, Polynomial.eval_one]
  apply Finset.sum_congr rfl
  intro k hk
  rw [bernstein_apply]
  simp only [smul_eq_mul]
  ring
