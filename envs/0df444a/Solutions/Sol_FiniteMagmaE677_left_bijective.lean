-- Prove2me | solution 1 for FiniteMagmaE677.left_bijective
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T01:36:25.430046+00:00
-- url     : https://prove2.me/submissions/42551f92-ec5b-4bef-b52f-7df6466a5958

import Definitions.Def_FiniteMagmaE677
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false

universe u

/-!
This formalizes the argument in the Equational Theories Project blueprint,
Chapter 13, Lemma 13.1(i): E677 makes each left multiplication surjective;
finiteness then makes it bijective.
Source: https://teorth.github.io/equational_theories/blueprint/677-chapter.html
-/

theorem solution {α : Type u} [Fintype α] (op : α → α → α)
    (h : FiniteMagmaE677.E677 op) (y : α) : Function.Bijective (op y) := by
  have hsurj : Function.Surjective (op y) := by
    intro x
    exact ⟨op x (op (op y x) y), (h x y).symm⟩
  exact (Finite.surjective_iff_bijective (f := op y)).mp hsurj

example : ∀ {α : Type u} [Fintype α] (op : α → α → α)
    (h : FiniteMagmaE677.E677 op) (y : α), Function.Bijective (op y) := @solution.{u}

#print axioms solution
