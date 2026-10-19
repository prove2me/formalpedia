-- Prove2me | solution 2 for ExplicitExpanders.Attach.cauchy_schwarz_R
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T20:23:43.803507+00:00
-- url     : https://prove2.me/submissions/7b85941e-9e16-4dae-8c69-6bbdc7f07816

import Mathlib
set_option autoImplicit false

theorem solution {V : Type*} [Fintype V] {r : ℕ} (f : V ⊕ Fin r → ℝ)
    (hf : ∑ u, f u = 0) :
    (∑ v, f (Sum.inl v)) ^ 2 = (∑ i, f (Sum.inr i)) ^ 2 ∧
      (∑ i, f (Sum.inr i)) ^ 2 ≤ (r : ℝ) * ∑ i, f (Sum.inr i) ^ 2 := by
  rw [Fintype.sum_sum_type] at hf
  refine ⟨?_, ?_⟩
  · have h : ∑ v, f (Sum.inl v) = -∑ i, f (Sum.inr i) := by linarith
    rw [h]; ring
  · have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin r))) (f := fun i => f (Sum.inr i))
    simpa using this
