-- Prove2me | solution 1 for BookProof.QgHermiteCore.expBounded_pow
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:11:41.415897+00:00
-- url     : https://prove2.me/submissions/9e2c7d34-33c3-4960-b977-5690202a8786

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
set_option autoImplicit false

theorem solution (k : ℕ) :
    ∃ C c : ℝ, 0 ≤ c ∧ ∀ x : ℝ, |x ^ k| ≤ C * Real.exp (c * ‖x‖) := by
  refine ⟨k.factorial, 1, zero_le_one, ?_⟩
  intro x
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  have h := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) k
  rw [div_le_iff₀ hfac] at h
  simpa only [abs_pow, one_mul, Real.norm_eq_abs, mul_comm, mul_one] using h
#print axioms solution
