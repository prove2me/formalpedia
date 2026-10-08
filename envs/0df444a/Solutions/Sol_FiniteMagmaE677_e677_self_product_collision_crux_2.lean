-- Prove2me | solution 2 for FiniteMagmaE677.e677_self_product_collision_crux
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T01:46:32.613316+00:00
-- url     : https://prove2.me/submissions/ab4fc2fc-fce7-4dc1-9286-ae4e0028a9c2

import Definitions.Def_FiniteMagmaE677
import Mathlib

set_option autoImplicit false

universe u

open FiniteMagmaE677

namespace SelfProductCruxInline

theorem L_bijective {α : Type u} [Fintype α] (op : α → α → α)
    (h : E677 op) (y : α) : Function.Bijective (op y) := by
  have hsurj : Function.Surjective (op y) := by
    intro a
    exact ⟨op a (op (op y a) y), (h a y).symm⟩
  exact Finite.surjective_iff_bijective.mp hsurj

theorem key_identity {α : Type u} [Fintype α] (op : α → α → α)
    (h : E677 op) (x y : α) :
    x = op (op y x) (op (op y (op y x)) y) := by
  have h1 := h (op y x) y
  exact (L_bijective op h y).1 h1

theorem crux_01 {α : Type u} [Fintype α] (op : α → α → α)
    (h : E677 op) (x : α) (hcoll : op (op x x) x = op x x) : op x x = x := by
  have hinj : ∀ y, Function.Injective (op y) := fun y => (L_bijective op h y).1
  have step1 : x = op x (op x (op x x)) := by
    have e_xx := h x x
    rw [hcoll] at e_xx
    exact e_xx
  by_cases hs : op x x = x
  · exact hs
  · by_cases h2 : op x (op x x) = x
    · have hcon : x = op x x := by
        calc x = op x (op x (op x x)) := step1
          _ = op x x := by rw [h2]
      exact absurd hcon.symm hs
    · have hxt : op x (op x (op x x)) = x := step1.symm
      have e_ts : op (op x (op x x)) (op x x) = op x x := by
        have e1 := h (op x (op x x)) x
        have r1 : op (op x (op x (op x x))) x = op x x := by rw [hxt]
        rw [r1] at e1
        have e2 : op x (op (op x (op x x)) (op x x)) = op x (op x x) := by rw [← e1]
        exact hinj x e2
      have e_st : op (op x x) (op x (op x x)) = x := by
        have k1 := key_identity op h (op x x) (op x (op x x))
        simp only [e_ts] at k1
        have e2 : op (op x x) (op (op x x) (op x (op x x))) = op (op x x) x := by rw [← k1, hcoll]
        exact hinj (op x x) e2
      have e_ss : op (op x x) (op x x) = op x x := by
        have k2 := key_identity op h (op x (op x x)) (op x x)
        simp only [e_st, hcoll] at k2
        have e2 : op x (op (op x x) (op x x)) = op x (op x x) := by rw [← k2]
        exact hinj x e2
      have e_sss := h (op x x) (op x x)
      have f1 : op (op x x) (op (op (op x x) (op x x)) (op x x)) = x := by
        have e2 : op (op x x) (op (op x x) (op (op (op x x) (op x x)) (op x x))) = op (op x x) x := by
          rw [← e_sss, hcoll]
        exact hinj (op x x) e2
      simp only [e_ss] at f1
      exact absurd f1 hs

end SelfProductCruxInline

open SelfProductCruxInline in
theorem solution {α : Type u} [Fintype α]
    (op : α → α → α) (h677 : E677 op) (x : α)
    (_hinj : Function.Injective (op x))
    (_h3 : (op x)^[3] x = x)
    (hcoll : op (op x x) x = op x x) :
    op x x = x :=
  crux_01 op h677 x hcoll
