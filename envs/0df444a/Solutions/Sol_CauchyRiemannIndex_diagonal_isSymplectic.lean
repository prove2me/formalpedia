-- Prove2me | solution 1 for CauchyRiemannIndex.diagonal_isSymplectic
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T17:36:46.591802+00:00
-- url     : https://prove2.me/submissions/c5b54c2b-7c2d-4692-bcec-b8aed112ae08

import Definitions.Def_CauchyRiemannIndex_Setting

open Matrix

namespace CauchyRiemannIndex

/-- A diagonal matrix with `d (inl k) * d (inr k) = 1` is symplectic. -/
theorem diagonal_isSymplectic_aux {n : ℕ} (d : Fin n ⊕ Fin n → ℝ)
    (hd : ∀ k, d (Sum.inl k) * d (Sum.inr k) = 1) : IsSymplectic (Matrix.diagonal d) := by
  unfold IsSymplectic
  rw [SymplecticGroup.mem_iff, diagonal_transpose]
  ext i j
  rw [mul_diagonal, diagonal_mul]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.J, Matrix.one_apply]
  · split_ifs with h
    · subst h; linarith [hd i]
    · rfl
  · split_ifs with h
    · subst h; linarith [hd i]
    · rfl

end CauchyRiemannIndex

open CauchyRiemannIndex in
theorem solution {n : ℕ} (d : Fin n ⊕ Fin n → ℝ)
    (hd : ∀ k, d (Sum.inl k) * d (Sum.inr k) = 1) : IsSymplectic (Matrix.diagonal d) :=
  CauchyRiemannIndex.diagonal_isSymplectic_aux d hd
