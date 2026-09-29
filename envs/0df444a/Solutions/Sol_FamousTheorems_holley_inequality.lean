-- Prove2me | solution 1 for FamousTheorems.holley_inequality
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:23:15.564988+00:00
-- url     : https://prove2.me/submissions/39305b54-26f3-4f66-8023-a290af70f028

import Mathlib

theorem solution {α : Type*} [DistribLattice α] [Fintype α] (f g μ : α → ℝ) (hμ₀ : 0 ≤ μ) (hf₀ : 0 ≤ f) (hg₀ : 0 ≤ g)
    (hμ : Monotone μ) (hfg : ∑ a, f a = ∑ a, g a) (h : ∀ a b, f a * g b ≤ f (a ⊓ b) * g (a ⊔ b)) :
    ∑ a, μ a * f a ≤ ∑ a, μ a * g a :=
  holley f g μ hμ₀ hf₀ hg₀ hμ hfg h
