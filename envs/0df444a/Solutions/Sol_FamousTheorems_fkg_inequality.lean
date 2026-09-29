-- Prove2me | solution 1 for FamousTheorems.fkg_inequality
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:00:44.709417+00:00
-- url     : https://prove2.me/submissions/86a575ac-29e7-47c2-9859-8ba97e0d6337

import Mathlib

theorem solution {α : Type*} [DistribLattice α] [Fintype α] (f g μ : α → ℝ) (hμ₀ : 0 ≤ μ) (hf₀ : 0 ≤ f) (hg₀ : 0 ≤ g)
    (hf : Monotone f) (hg : Monotone g) (hμ : ∀ a b, μ a * μ b ≤ μ (a ⊓ b) * μ (a ⊔ b)) :
    (∑ a, μ a * f a) * ∑ a, μ a * g a ≤ (∑ a, μ a) * ∑ a, μ a * (f a * g a) :=
  fkg f g μ hμ₀ hf₀ hg₀ hf hg hμ
