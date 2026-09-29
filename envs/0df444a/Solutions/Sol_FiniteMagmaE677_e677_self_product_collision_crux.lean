-- Prove2me | solution 1 for FiniteMagmaE677.e677_self_product_collision_crux
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-24T01:37:59.449009+00:00
-- url     : https://prove2.me/submissions/47b3b9d4-7f24-4895-93d1-7fa750892309

import Definitions.Def_FiniteMagmaE677
import Mathlib

set_option autoImplicit false

universe u

open FiniteMagmaE677

-- Lemma 13.1(i): every left translation is bijective (E677 + Fintype)
theorem L_bijective {α : Type u} [Fintype α] (op : α → α → α)
    (h : E677 op) (y : α) : Function.Bijective (op y) := by
  have hsurj : Function.Surjective (op y) := by
    intro a
    exact ⟨op a (op (op y a) y), (h a y).symm⟩
  exact Finite.surjective_iff_bijective.mp hsurj

-- Lemma 13.1(iii): x = (L_y x) ⋄ (R_y (L_y² x))
theorem key_identity {α : Type u} [Fintype α] (op : α → α → α)
    (h : E677 op) (x y : α) :
    x = op (op y x) (op (op y (op y x)) y) := by
  have h1 := h (op y x) y
  exact (L_bijective op h y).1 h1

-- (0,1)-crux: op (op x x) x = op x x  →  op x x = x
theorem crux_01 {α : Type u} [Fintype α] (op : α → α → α)
    (h : E677 op) (x : α) (hcoll : op (op x x) x = op x x) :
    op x x = x := by
  have hinj : ∀ y, Function.Injective (op y) := fun y => (L_bijective op h y).1
  -- Step 1: E677(x,x) + hcoll gives x = op x (op x (op x x)), i.e. L_x³ x = x
  have step1 : x = op x (op x (op x x)) := by
    have e_xx := h x x
    rw [hcoll] at e_xx
    exact e_xx
  by_cases hs : op x x = x
  · exact hs
  · -- s := op x x ≠ x
    by_cases h2 : op x (op x x) = x
    · -- |C| = 2 case: L_x (op x x) = x, so x = op x (op x s) = op x x, contradiction
      have hcon : x = op x x := by
        calc x = op x (op x (op x x)) := step1
          _ = op x x := by rw [h2]
      exact absurd hcon.symm hs
    · -- |C| = 3 case: derive a contradiction via the equational chain
      -- Abbreviations: s = op x x, t = op x s.  We have op x t = x.
      have hxt : op x (op x (op x x)) = x := step1.symm
      -- (1) op t s = s, where t = op x (op x x), s = op x x
      -- E677(t,x): t = op x (op t (op (op x t) x));  op x t = x so op (op x t) x = s
      have e_ts : op (op x (op x x)) (op x x) = op x x := by
        have e1 := h (op x (op x x)) x
        -- e1 : t = op x (op t (op (op x t) x))
        have r1 : op (op x (op x (op x x))) x = op x x := by rw [hxt]
        -- op (op x t) x = op x x = s
        rw [r1] at e1
        -- e1 : t = op x (op t s)
        -- op x s = t, so op x (op t s) = op x s → op t s = s by injectivity
        have e2 : op x (op (op x (op x x)) (op x x)) = op x (op x x) := by
          rw [← e1]
        exact hinj x e2
      -- (2) op s t = x.  key_identity(s,t): s = op (op t s) (op (op t (op t s)) t)
      -- with op t s = s: s = op s (op s t).  Also s = op s x by hcoll.
      have e_st : op (op x x) (op x (op x x)) = x := by
        have k1 := key_identity op h (op x x) (op x (op x x))
        -- k1 : s = op (op t s) (op (op t (op t s)) t)
        simp only [e_ts] at k1
        -- k1 : s = op s (op s t)
        -- hcoll : op s x = s, so op s (op s t) = op s x
        have e2 : op (op x x) (op (op x x) (op x (op x x))) = op (op x x) x := by
          rw [← k1, hcoll]
        exact hinj (op x x) e2
      -- (3) op s s = s.  key_identity(t,s): t = op (op s t) (op (op s (op s t)) s)
      -- with op s t = x: t = op x (op (op s x) s) = op x (op s s) by hcoll.
      -- Also t = op x s.  Injectivity of op x gives op s s = s.
      have e_ss : op (op x x) (op x x) = op x x := by
        have k2 := key_identity op h (op x (op x x)) (op x x)
        -- k2 : t = op (op s t) (op (op s (op s t)) s)
        simp only [e_st, hcoll] at k2
        -- k2 : t = op x (op s s)
        -- t = op x s, so op x (op s s) = op x s
        have e2 : op x (op (op x x) (op x x)) = op x (op x x) := by
          rw [← k2]
        exact hinj x e2
      -- (4) Final contradiction.
      -- E677(s,s): s = op s (op s (op (op s s) s)).
      -- So op s (op s (op (op s s) s)) = s = op s x  →  op s (op (op s s) s) = x.
      -- With op s s = s: op (op s s) s = s, so op s s = x, i.e. s = x. Contradiction.
      have e_sss := h (op x x) (op x x)
      -- e_sss : s = op s (op s (op (op s s) s))
      have f1 : op (op x x) (op (op (op x x) (op x x)) (op x x)) = x := by
        have e2 : op (op x x) (op (op x x) (op (op (op x x) (op x x)) (op x x)))
            = op (op x x) x := by
          rw [← e_sss, hcoll]
        exact hinj (op x x) e2
      -- f1 : op s (op (op s s) s) = x.  Rewrite op s s = s via e_ss.
      simp only [e_ss] at f1
      -- f1 : s = x. Contradiction with hs.
      exact absurd f1 hs

-- Platform-facing solution: exact statement match with theorem node
-- FiniteMagmaE677.e677_self_product_collision_crux
-- (1c6e797c-612e-40e2-8068-adf0f0cf4d21). The extra hypotheses hinj and h3
-- are not needed: crux_01 derives them from E677 on a finite type.
theorem solution {α : Type u} [Fintype α]
    (op : α → α → α) (h677 : FiniteMagmaE677.E677 op) (x : α)
    (hinj : Function.Injective (op x))
    (h3 : (op x)^[3] x = x)
    (hcoll : op (op x x) x = op x x) :
    op x x = x := by
  exact crux_01 op h677 x hcoll
