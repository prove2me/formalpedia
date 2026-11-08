-- Prove2me | solution 1 for DPDeconstructed.lemma_6_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:54:20.823261+00:00
-- url     : https://prove2.me/submissions/14c85380-d5a2-4074-9dda-2bd33b8a00dd

import Mathlib

theorem solution {E₀ E₁ E₂ : Type*} [Nonempty E₀] [Nonempty E₁] [Nonempty E₂]
    (τ₀ : E₀ → E₁) (τ₁ : E₁ → E₂) (τ₂ : E₂ → E₀) :
    (∀ ϱ : E₀, (τ₂ ∘ τ₁ ∘ τ₀) ϱ = ϱ → (τ₀ ∘ τ₂ ∘ τ₁) (τ₀ ϱ) = τ₀ ϱ) ∧
      ∀ n : ℕ, ∀ e : E₀, (τ₀ ∘ τ₂ ∘ τ₁)^[n] (τ₀ e) = τ₀ ((τ₂ ∘ τ₁ ∘ τ₀)^[n] e) := by
  refine ⟨fun ϱ h => ?_, fun n e => ?_⟩
  · have := congrArg τ₀ h
    simpa using this
  · have hs : Function.Semiconj τ₀ (τ₂ ∘ τ₁ ∘ τ₀) (τ₀ ∘ τ₂ ∘ τ₁) := fun _ => rfl
    exact (hs.iterate_right n e).symm
