-- Prove2me | solution 1 for BookProof.QgHermiteCore.expBounded_poly
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:22:24.728092+00:00
-- url     : https://prove2.me/submissions/05b73b8e-e372-4645-95f2-7c67693aa594

import Definitions.Def_ChapterHermiteFunctions
set_option autoImplicit false

theorem solution (p : Polynomial ℝ) :
    ∃ C c : ℝ, 0 ≤ c ∧ ∀ x : ℝ, |p.eval x| ≤ C * Real.exp (c * ‖x‖) := by
  refine ⟨∑ k ∈ p.support, |p.coeff k| * (k.factorial : ℝ), 1, zero_le_one, ?_⟩
  intro x
  simp only [one_mul, Real.norm_eq_abs]
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  calc
    |∑ k ∈ p.support, p.coeff k * x ^ k| ≤ ∑ k ∈ p.support, |p.coeff k * x ^ k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ p.support, (|p.coeff k| * (k.factorial : ℝ)) * Real.exp |x| := by
      apply Finset.sum_le_sum
      intro k hk
      have hfac : (0 : ℝ) < (k.factorial : ℝ) := by positivity
      have h := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) k
      rw [div_le_iff₀ hfac] at h
      rw [abs_mul, abs_pow, mul_assoc]
      exact mul_le_mul_of_nonneg_left (by simpa only [mul_comm] using h) (abs_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm
#print axioms solution
