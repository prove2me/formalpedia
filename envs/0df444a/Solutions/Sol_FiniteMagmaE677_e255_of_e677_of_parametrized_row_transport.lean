-- Prove2me | solution 1 for FiniteMagmaE677.e255_of_e677_of_parametrized_row_transport
-- status  : ACCEPTED   (prove)
-- author  : @omegaestable
-- created : 2026-10-14T04:16:21.858035+00:00
-- url     : https://prove2.me/submissions/fb8a625a-e3f1-459d-82b0-f99675c2a78a

import Mathlib.Data.Fintype.Card
import Theorems.Thm_FiniteMagmaE677_fixer_unique

set_option autoImplicit false

universe u

theorem solution {α : Type u} [Fintype α]
    (op : α → α → α)
    (h : FiniteMagmaE677.E677 op)
    (hPRT : ∀ x a : α, ∃ c e : α,
      op (op a e) (op c (op x (op x (op (op a x) a)))) = op (op x e) x) :
    FiniteMagmaE677.E255 op := by
  classical
  have inj (y : α) : Function.Injective (op y) := by
    have hs : Set.SurjOn (op y) (↑(Finset.univ : Finset α))
        (↑(Finset.univ : Finset α)) := by
      intro x _
      exact ⟨op x (op (op y x) y), Finset.mem_univ _, (h x y).symm⟩
    have hi := Finset.injOn_of_surjOn_of_card_le (op y)
      (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _) hs (by rfl)
    intro a b hab
    exact hi (Finset.mem_univ a) (Finset.mem_univ b) hab
  intro x
  obtain ⟨c, e, hce⟩ := hPRT x x
  have hdiag : op x (op x (op (op x x) x)) = x := (h x x).symm
  have hrow : op (op x e) (op c x) = op (op x e) x := by
    simpa only [hdiag] using hce
  have hfix : op c x = x := inj (op x e) hrow
  rw [← FiniteMagmaE677.fixer_unique op h x c hfix]
  exact hfix.symm
