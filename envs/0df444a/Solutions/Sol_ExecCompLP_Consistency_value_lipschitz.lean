-- Prove2me | solution 1 for ExecCompLP.Consistency.value_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:57:27.947991+00:00
-- url     : https://prove2.me/submissions/0a887c87-0f84-4423-8845-991b91bcdc79

import Mathlib
set_option autoImplicit false

theorem solution {n : ℕ} (c : Fin n → ℝ) :
    ∃ B > 0, ∀ α a : Fin n → ℝ, |∑ j, c j * (α j - a j)| ≤ B * ‖α - a‖ := by
  refine ⟨∑ j, |c j| + 1, by positivity, ?_⟩
  intro α a
  have hnn : 0 ≤ ‖α - a‖ := norm_nonneg _
  calc |∑ j, c j * (α j - a j)| ≤ ∑ j, |c j * (α j - a j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |c j| * ‖α - a‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have := norm_le_pi_norm (α - a) j
        simpa using this
    _ = (∑ j, |c j|) * ‖α - a‖ := by rw [Finset.sum_mul]
    _ ≤ (∑ j, |c j| + 1) * ‖α - a‖ := by nlinarith
