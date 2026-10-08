-- Prove2me | solution 1 for ExplicitExpanders.Attach.eq_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T01:45:17.228443+00:00
-- url     : https://prove2.me/submissions/1a5a0b51-3274-4289-ba50-e8ed9364f798

import Mathlib
import Definitions.Def_ExplicitExpanders_Attach_IsNDLambda
import Definitions.Def_ExplicitExpanders_Attach_attachMatrix

open Matrix in
theorem ExplicitExpanders.Attach.eq_4_aux {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (W : Fin r → Finset V) (f : V ⊕ Fin r → ℝ) :
    f ⬝ᵥ (ExplicitExpanders.Attach.matL W *ᵥ f) =
      ∑ v ∈ ExplicitExpanders.Attach.loopSet W, f (Sum.inl v) ^ 2 := by
  have h1 : ∀ v : V, (ExplicitExpanders.Attach.matL W *ᵥ f) (Sum.inl v)
      = (if v ∈ ExplicitExpanders.Attach.loopSet W then (1 : ℝ) else 0) * f (Sum.inl v) := by
    intro v
    simp [ExplicitExpanders.Attach.matL, mulVec, dotProduct, Fintype.sum_sum_type,
      fromBlocks, diagonal]
  have h2 : ∀ i : Fin r, (ExplicitExpanders.Attach.matL W *ᵥ f) (Sum.inr i) = 0 := by
    intro i
    simp [ExplicitExpanders.Attach.matL, mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks]
  rw [dotProduct, Fintype.sum_sum_type]
  simp only [h1, h2, mul_zero, Finset.sum_const_zero, add_zero]
  have h3 : ∀ v : V, f (Sum.inl v) *
      ((if v ∈ ExplicitExpanders.Attach.loopSet W then (1 : ℝ) else 0) * f (Sum.inl v))
      = if v ∈ ExplicitExpanders.Attach.loopSet W then f (Sum.inl v) ^ 2 else 0 := by
    intro v; split_ifs <;> ring
  simp_rw [h3]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

open ExplicitExpanders.Attach Matrix in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ} (W : Fin r → Finset V)
    (f : V ⊕ Fin r → ℝ) :
    f ⬝ᵥ (matL W *ᵥ f) = ∑ v ∈ loopSet W, f (Sum.inl v) ^ 2 := by
  exact ExplicitExpanders.Attach.eq_4_aux W f
