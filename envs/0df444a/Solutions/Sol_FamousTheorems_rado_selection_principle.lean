-- Prove2me | solution 1 for FamousTheorems.rado_selection_principle
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:16:04.756872+00:00
-- url     : https://prove2.me/submissions/d33ea9d0-a195-425c-9153-0800c2502821

import Mathlib

theorem solution {α : Type*} {β : α → Type*} [∀ a, Finite (β a)] (g : Finset α → (a : α) → β a) :
    ∃ χ : (a : α) → β a, ∀ s : Finset α, ∃ t : Finset α, s ⊆ t ∧ ∀ x ∈ s, χ x = g t x :=
  Finset.rado_selection g
