-- Prove2me | solution 1 for CliqueNP.chooseOccurrenceRepresentatives
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T11:21:56.410986+00:00
-- url     : https://prove2.me/submissions/8f24909e-eb3e-4a7b-9349-dea3fb802b8a

import Mathlib
set_option autoImplicit false
theorem solution
    {α β γ : Type}
    (P : α → β → Prop)
    (Q : α → β → γ → Prop)
    (h : ∀ a, ∃ b, P a b ∧ ∃ c, Q a b c) :
    ∃ f : α → β, (∀ a, P a (f a)) ∧
      (∀ a, ∃ c, Q a (f a) c) := by
  choose f hf using h
  exact ⟨f, fun a => (hf a).1, fun a => (hf a).2⟩
