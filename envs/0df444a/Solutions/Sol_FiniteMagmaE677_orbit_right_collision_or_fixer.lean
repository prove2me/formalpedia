-- Prove2me | solution 1 for FiniteMagmaE677.orbit_right_collision_or_fixer
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T00:37:24.09727+00:00
-- url     : https://prove2.me/submissions/a5b680bf-f463-4e9d-be90-8be712433c50
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_FiniteMagmaE677
import Theorems.Thm_FiniteMagmaE677_e677_orbit_collision_reduces_to_crux
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false

universe u

open FiniteMagmaE677

namespace SelfProductCruxPrivate

theorem L_bijective {α : Type u} [Fintype α] (op : α → α → α)
    (h : E677 op) (y : α) : Function.Bijective (op y) := by
  have hsurj : Function.Surjective (op y) :=
    fun a => ⟨op a (op (op y a) y), (h a y).symm⟩
  exact Finite.surjective_iff_bijective.mp hsurj

theorem key_identity {α : Type u} [Fintype α] (op : α → α → α)
    (h : E677 op) (x y : α) :
    x = op (op y x) (op (op y (op y x)) y) := by
  exact (L_bijective op h y).1 (h (op y x) y)

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

end SelfProductCruxPrivate

open SelfProductCruxPrivate

private theorem self_product_collision_gives_fixer {α : Type u} [Fintype α]
    (op : α → α → α) (h : E677 op) (x : α)
    (hself : op (op x x) x = op x x) : HasFixerAt op x := by
  exact ⟨x, crux_01 op h x hself⟩

theorem solution {α : Type u} [Fintype α] (op : α → α → α) (h : E677 op) (x : α) :
    OrbitRightCollisionOrFixer op x := by
  intro a b ha hb hab
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  have hcoll : op ((op x)^[i] x) x = op ((op x)^[j] x) x := by
    simpa [hi, hj] using hab
  rcases e677_orbit_collision_reduces_to_crux op h x i j hcoll with heq | hself | hfix
  · left
    simpa [hi, hj, heq]
  · right
    exact self_product_collision_gives_fixer op h x hself
  · right
    exact hfix
