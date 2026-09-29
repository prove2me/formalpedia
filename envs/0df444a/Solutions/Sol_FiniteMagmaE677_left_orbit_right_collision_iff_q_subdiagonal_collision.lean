-- Prove2me | solution 1 for FiniteMagmaE677.left_orbit_right_collision_iff_q_subdiagonal_collision
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-15T04:34:52.14224+00:00
-- url     : https://prove2.me/submissions/e6f7b6e9-7756-45f8-84c8-99db783b5fc6

import Definitions.Def_FiniteMagmaE677
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

universe u

private theorem qSubdiag_eq_rightTranslation
    {α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
    (x : α) (k : ℕ) :
    op ((op x)^[k] x)
        (op (op ((op x)^[k + 1] x) ((op x)^[k] x)) ((op x)^[k + 1] x)) =
      op ((op x)^[k + 2] x) x := by
  have hinj : ∀ z : α, Function.Injective (op z) := by
    intro z
    have hs : Function.Surjective (op z) :=
      fun p => ⟨op p (op (op z p) z), (h p z).symm⟩
    exact (Finite.surjective_iff_bijective.mp hs).1
  have h1 : (op x)^[k + 1] x = op x ((op x)^[k] x) :=
    Function.iterate_succ_apply' (op x) k x
  have h2 : (op x)^[k + 2] x = op x (op x ((op x)^[k] x)) := by
    rw [← h1]
    exact Function.iterate_succ_apply' (op x) (k + 1) x
  rw [h1, h2]
  generalize (op x)^[k] x = a
  have hrec : a = op (op x a) (op (op x (op x a)) x) :=
    hinj x (h (op x a) x)
  apply hinj (op x a)
  rw [← hrec]
  exact (h a (op x a)).symm

theorem solution
    {α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
    (x : α) (i j : ℕ) :
    op ((op x)^[i + 2] x) x = op ((op x)^[j + 2] x) x ↔
      op ((op x)^[i] x)
          (op (op ((op x)^[i + 1] x) ((op x)^[i] x)) ((op x)^[i + 1] x)) =
        op ((op x)^[j] x)
          (op (op ((op x)^[j + 1] x) ((op x)^[j] x)) ((op x)^[j + 1] x)) := by
  rw [qSubdiag_eq_rightTranslation op h x i, qSubdiag_eq_rightTranslation op h x j]
