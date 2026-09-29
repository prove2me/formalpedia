-- Prove2me | solution 1 for FamousTheorems.ahlswede_daykin
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:22:26.713373+00:00
-- url     : https://prove2.me/submissions/24308029-98a1-49b1-a3b9-ecb386dd4b81

import Mathlib

open scoped FinsetFamily

theorem solution {α β : Type*} [DistribLattice α] [CommSemiring β] [LinearOrder β] [IsStrictOrderedRing β] [ExistsAddOfLE β]
    (f₁ f₂ f₃ f₄ : α → β) [DecidableEq α] (h₁ : 0 ≤ f₁) (h₂ : 0 ≤ f₂) (h₃ : 0 ≤ f₃) (h₄ : 0 ≤ f₄)
    (h : ∀ a b, f₁ a * f₂ b ≤ f₃ (a ⊓ b) * f₄ (a ⊔ b)) (s t : Finset α) :
    (∑ a ∈ s, f₁ a) * (∑ a ∈ t, f₂ a) ≤ (∑ a ∈ s ⊼ t, f₃ a) * (∑ a ∈ s ⊻ t, f₄ a) :=
  four_functions_theorem f₁ f₂ f₃ f₄ h₁ h₂ h₃ h₄ h s t
