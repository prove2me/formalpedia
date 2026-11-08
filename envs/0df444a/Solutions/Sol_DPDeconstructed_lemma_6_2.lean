-- Prove2me | solution 1 for DPDeconstructed.lemma_6_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:55:07.319294+00:00
-- url     : https://prove2.me/submissions/38bb021a-d829-4968-8d96-2a9168c076f7

import Mathlib

theorem solution {E₀ E₁ E₂ : Type*} [Nonempty E₀] [Nonempty E₁] [Nonempty E₂]
    (τ₀ : E₀ → E₁) (τ₁ : E₁ → E₂) (τ₂ : E₂ → E₀) (ϱ₀ : E₀)
    (hfix : (τ₂ ∘ τ₁ ∘ τ₀) ϱ₀ = ϱ₀) (huniq : ∀ e : E₀, (τ₂ ∘ τ₁ ∘ τ₀) e = e → e = ϱ₀) :
    (τ₀ ∘ τ₂ ∘ τ₁) (τ₀ ϱ₀) = τ₀ ϱ₀ ∧ ∀ f : E₁, (τ₀ ∘ τ₂ ∘ τ₁) f = f → f = τ₀ ϱ₀ := by
  refine ⟨?_, fun f hf => ?_⟩
  · have := congrArg τ₀ hfix
    simpa using this
  · have hf' : τ₀ (τ₂ (τ₁ f)) = f := hf
    have he : (τ₂ ∘ τ₁ ∘ τ₀) (τ₂ (τ₁ f)) = τ₂ (τ₁ f) := by
      simp only [Function.comp_apply, hf']
    have := huniq _ he
    rw [← hf', this]
