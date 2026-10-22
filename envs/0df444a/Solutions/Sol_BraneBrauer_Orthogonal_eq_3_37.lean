-- Prove2me | solution 1 for BraneBrauer.Orthogonal.eq_3_37
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T21:01:48.248802+00:00
-- url     : https://prove2.me/submissions/0f40d427-f6ab-4098-be53-d96b50440a04

import Mathlib
import Definitions.Def_BraneBrauer_Orthogonal_Setting

noncomputable section
open BraneBrauer.Orthogonal

lemma iffX {k N : ℕ} (σ : Equiv.Perm (Fin k)) (x s : Fin k → Fin N) :
    (x = s ∘ ⇑σ.symm) ↔ (s = x ∘ ⇑σ) := by
  constructor
  · rintro rfl; funext i; simp
  · rintro rfl; funext i; simp

lemma conjX {N m n : ℕ} (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) (X : Op N m n) :
    permOp N m n σ τ * X * permOp N m n σ⁻¹ τ⁻¹ =
      Matrix.of fun r c => X (r.1 ∘ σ, r.2 ∘ τ) (c.1 ∘ σ, c.2 ∘ τ) := by
  ext ⟨x, y⟩ ⟨x', y'⟩
  simp only [Matrix.mul_apply, permOp, Matrix.kroneckerMap_apply, Matrix.kronecker,
    QAlgorithms.Schur.tensorPermutation, Matrix.of_apply, Fintype.sum_prod_type]
  simp [iffX, ite_mul, mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq, Equiv.Perm.inv_def]

lemma sigma_sigmaX {N m n : ℕ} (X : Op N m n) : sigma (sigma X) = X := by
  ext ⟨x, y⟩ ⟨x', y'⟩; rfl

theorem solution {N m n : ℕ}
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n))
    (X : Op N m n) :
    (permOp N m n σ τ * X * permOp N m n σ⁻¹ τ⁻¹ = X) ↔
    (permOp N m n σ τ * sigma X * permOp N m n σ⁻¹ τ⁻¹ = sigma X) := by
  have key : ∀ Y : Op N m n, sigma (permOp N m n σ τ * Y * permOp N m n σ⁻¹ τ⁻¹) =
      permOp N m n σ τ * sigma Y * permOp N m n σ⁻¹ τ⁻¹ := by
    intro Y
    rw [conjX, conjX]
    ext ⟨x, y⟩ ⟨x', y'⟩; rfl
  constructor
  · intro h; rw [← key, h]
  · intro h
    have := congrArg sigma h
    rwa [← key, sigma_sigmaX, sigma_sigmaX] at this
