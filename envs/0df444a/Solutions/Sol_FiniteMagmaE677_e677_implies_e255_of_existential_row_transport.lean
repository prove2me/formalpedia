-- Prove2me | solution 1 for FiniteMagmaE677.e677_implies_e255_of_existential_row_transport
-- status  : ACCEPTED   (prove)
-- author  : @omegaestable
-- created : 2026-10-14T00:34:28.756291+00:00
-- url     : https://prove2.me/submissions/aa7fd765-72ae-4ab1-b148-bc2f1ba7f9b5

import Theorems.Thm_FiniteMagmaE677_fixer_unique

set_option autoImplicit false
universe u

theorem solution {α : Type u} [Fintype α]
    (op : α → α → α)
    (h : ∀ x y : α, x = op y (op x (op (op y x) y)))
    (hER : ∀ x : α, ∃ b : α, ∀ a : α, ∃ c : α,
      op c (op b (op x (op (op a x) a))) = x) :
    ∀ x : α, x = op (op (op x x) x) x := by
  intro x
  obtain ⟨b, hb⟩ := hER x
  obtain ⟨r, hr⟩ := hb b
  have fix : op r x = x := by
    simpa only [← h x b] using hr
  rw [← FiniteMagmaE677.fixer_unique op h x r fix]
  exact fix.symm
