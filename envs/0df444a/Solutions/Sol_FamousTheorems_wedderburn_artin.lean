-- Prove2me | solution 1 for FamousTheorems.wedderburn_artin
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T17:32:50.503299+00:00
-- url     : https://prove2.me/submissions/c0e462f3-e81e-4948-b499-7a4715bbd896

import Mathlib

universe u v

theorem solution (R₀ : Type v) (R : Type u) [CommSemiring R₀] [Ring R] [Algebra R₀ R] [IsSemisimpleRing R] :
    ∃ (n : ℕ) (D : Fin n → Type u) (d : Fin n → ℕ) (_ : ∀ i, DivisionRing (D i)) (_ : ∀ i, Algebra R₀ (D i)),
      (∀ i, NeZero (d i)) ∧ Nonempty (R ≃ₐ[R₀] ((i : Fin n) → Matrix (Fin (d i)) (Fin (d i)) (D i))) :=
  IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing R₀ R
