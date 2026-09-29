-- Prove2me | solution 1 for FamousTheorems.eckmann_hilton_argument
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:11:07.805049+00:00
-- url     : https://prove2.me/submissions/c94f204a-f62a-4bc0-876f-117a58d0a76c

import Mathlib

theorem solution {X : Type*} {m₁ m₂ : X → X → X} {e₁ e₂ : X} (h₁ : EckmannHilton.IsUnital m₁ e₁) (h₂ : EckmannHilton.IsUnital m₂ e₂)
    (distrib : ∀ a b c d, m₁ (m₂ a b) (m₂ c d) = m₂ (m₁ a c) (m₁ b d)) :
    m₁ = m₂ ∧ ∀ a b, m₂ a b = m₂ b a :=
  ⟨EckmannHilton.mul h₁ h₂ distrib, (EckmannHilton.mul_comm h₁ h₂ distrib).comm⟩
