-- Prove2me | solution 1 for ExplicitExpanders.Attach.cauchy_schwarz_R
-- status  : ACCEPTED   (prove)
-- author  : @Persea
-- created : 2026-10-18T14:53:59.612109+00:00
-- url     : https://prove2.me/submissions/f7054981-cb9d-4110-8e70-514e98851c94

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith

open scoped BigOperators
set_option autoImplicit false

theorem solution {V : Type*} [Fintype V] {r : ℕ} (f : V ⊕ Fin r → ℝ)
    (hf : ∑ u, f u = 0) :
    (∑ v, f (Sum.inl v)) ^ 2 = (∑ i, f (Sum.inr i)) ^ 2 ∧
      (∑ i, f (Sum.inr i)) ^ 2 ≤ (r : ℝ) * ∑ i, f (Sum.inr i) ^ 2 := by
  have hsum : (∑ v, f (Sum.inl v)) + (∑ i, f (Sum.inr i)) = 0 := by
    simpa only [Fintype.sum_sum_type] using hf
  constructor
  · have heq : (∑ v, f (Sum.inl v)) = -(∑ i, f (Sum.inr i)) := by linarith
    rw [heq, neg_sq]
  · simpa using (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin r))
      (fun _ => (1 : ℝ)) (fun i => f (Sum.inr i)))


