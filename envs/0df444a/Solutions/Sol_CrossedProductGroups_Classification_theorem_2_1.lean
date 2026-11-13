-- Prove2me | solution 1 for CrossedProductGroups.Classification.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-13T02:51:49.666082+00:00
-- url     : https://prove2.me/submissions/f1f07d6d-8e48-4d71-91ec-17fc4ade574e

import Definitions.Def_CrossedProductGroups_Classification_CrossedSystem
import Theorems.Thm_CrossedProductGroups_Classification_lemma_1_2
import Mathlib.Tactic.Group
set_option autoImplicit false

open CrossedProductGroups.Classification


theorem solution {H G : Type*} [Group H] [Group G] (α : G → MulAut H) (f : G → G → H)
    (hc : IsCrossedSystem α f) (hn : f 1 1 = 1) (X : Type*) [Group X] :
    -- (1) `(H #^f_α G, (i_H, i_G))` is an object of `_ΓC` ...
    ((∀ h₁ h₂ : H, crossedMul α f (h₁, 1) (h₂, 1) = (h₁ * h₂, 1)) ∧
      (∀ g₁ g₂ : G, crossedMul α f (1, g₁) (1, g₂) = crossedMul α f (f g₁ g₂, 1) (1, g₁ * g₂)) ∧
      (∀ g : G, ∀ h : H, crossedMul α f (1, g) (h, 1) = crossedMul α f (α g h, 1) (1, g))) ∧
    -- ... and it is initial: a unique morphism to every object `(X, (u, v))` of `_ΓC`
    (∀ (u : H →* X) (v : G → X),
      (∀ g₁ g₂ : G, v g₁ * v g₂ = u (f g₁ g₂) * v (g₁ * g₂)) →
      (∀ g : G, ∀ h : H, v g * u h = u (α g h) * v g) →
      ∃! w : H × G → X, (∀ x y : H × G, w (crossedMul α f x y) = w x * w y) ∧
        (∀ h : H, w (h, 1) = u h) ∧ ∀ g : G, w (1, g) = v g) ∧
    -- (2) `(H #^f_α G, (π_H, π_G))` is an object of `C_Γ` ...
    ((∀ x y : H × G, (crossedMul α f x y).2 = x.2 * y.2) ∧
      (∀ x y : H × G, (crossedMul α f x y).1 = x.1 * α x.2 y.1 * f x.2 y.2)) ∧
    -- ... and it is final: a unique morphism from every object `(X, (u, v))` of `C_Γ`
    (∀ (v : X →* G) (u : X → H),
      (∀ x y : X, u (x * y) = u x * α (v x) (u y) * f (v x) (v y)) →
      ∃! w : X → H × G, (∀ x y : X, w (x * y) = crossedMul α f (w x) (w y)) ∧
        (∀ x : X, (w x).1 = u x) ∧ ∀ x : X, (w x).2 = v x) := by
  obtain ⟨hL,hA⟩ := (lemma_1_2 α f hc).2.2.2 hn
  have hfact (x : H × G) : crossedMul α f (x.1,1) (1,x.2) = x := by
    cases x with | mk h g => simp [crossedMul,hA,(hL g).1]
  refine ⟨?_,?_,⟨fun _ _ => rfl,fun _ _ => rfl⟩,?_⟩
  · refine ⟨?_,?_,?_⟩
    · intro a b
      simp [crossedMul,hA,hn]
    · intro g k
      simp [crossedMul,hA,(hL (g*k)).1]
    · intro g h
      simp [crossedMul,hA,(hL g).1,(hL g).2]
  · intro u v hvv hvu
    have hv1 : v 1 = 1 := by
      have hh := hvv 1 1
      simp only [hn,map_one,one_mul] at hh
      exact mul_eq_right.mp hh
    refine ⟨fun x => u x.1 * v x.2,⟨?_,?_,?_⟩,?_⟩
    · intro x y
      change u (x.1 * α x.2 y.1 * f x.2 y.2) * v (x.2*y.2) =
        (u x.1*v x.2)*(u y.1*v y.2)
      rw [map_mul,map_mul]
      calc
        _ = u x.1 * u (α x.2 y.1) * (u (f x.2 y.2) * v (x.2*y.2)) := by group
        _ = u x.1 * u (α x.2 y.1) * (v x.2 * v y.2) := by rw [hvv]
        _ = u x.1 * (u (α x.2 y.1) * v x.2) * v y.2 := by group
        _ = u x.1 * (v x.2 * u y.1) * v y.2 := by rw [hvu]
        _ = _ := by group
    · intro h
      simp [hv1]
    · intro g
      simp
    · intro w hw
      funext x
      calc
        w x = w (crossedMul α f (x.1,1) (1,x.2)) := congrArg w (hfact x).symm
        _ = w (x.1,1) * w (1,x.2) := hw.1 _ _
        _ = u x.1 * v x.2 := by rw [hw.2.1,hw.2.2]
  · intro v u hu
    refine ⟨fun x => (u x,v x),⟨?_,fun _ => rfl,fun _ => rfl⟩,?_⟩
    · intro x y
      exact Prod.ext (hu x y) (v.map_mul x y)
    · intro w hw
      funext x
      exact Prod.ext (hw.2.1 x) (hw.2.2 x)
