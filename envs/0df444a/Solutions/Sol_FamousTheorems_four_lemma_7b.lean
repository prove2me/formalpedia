-- Prove2me | solution 1 for FamousTheorems.four_lemma_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:18:02.755312+00:00
-- url     : https://prove2.me/submissions/d9d7c084-88f5-4ae7-97f5-e50dc48a22b5

import Mathlib

theorem solution {R M₁ M₂ M₃ M₄ N₁ N₂ N₃ N₄ : Type*} [CommRing R]
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup M₄]
    [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄]
    [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃] [AddCommGroup N₄]
    [Module R N₁] [Module R N₂] [Module R N₃] [Module R N₄]
    (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃) (f₃ : M₃ →ₗ[R] M₄)
    (g₁ : N₁ →ₗ[R] N₂) (g₂ : N₂ →ₗ[R] N₃) (g₃ : N₃ →ₗ[R] N₄)
    (i₁ : M₁ →ₗ[R] N₁) (i₂ : M₂ →ₗ[R] N₂) (i₃ : M₃ →ₗ[R] N₃) (i₄ : M₄ →ₗ[R] N₄)
    (hc₁ : g₁ ∘ₗ i₁ = i₂ ∘ₗ f₁) (hc₂ : g₂ ∘ₗ i₂ = i₃ ∘ₗ f₂) (hc₃ : g₃ ∘ₗ i₃ = i₄ ∘ₗ f₃)
    (hf : Function.Exact f₂ f₃) (hg₁ : Function.Exact g₁ g₂) (hg₂ : Function.Exact g₂ g₃)
    (hi₁ : Function.Surjective i₁) (hi₃ : Function.Surjective i₃) (hi₄ : Function.Injective i₄) :
    Function.Surjective i₂ :=
  LinearMap.surjective_of_surjective_of_surjective_of_injective f₁ f₂ f₃ g₁ g₂ g₃ i₁ i₂ i₃ i₄ hc₁ hc₂ hc₃ hf hg₁ hg₂ hi₁ hi₃ hi₄
