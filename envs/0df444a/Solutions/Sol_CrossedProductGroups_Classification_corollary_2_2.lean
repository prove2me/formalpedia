-- Prove2me | solution 1 for CrossedProductGroups.Classification.corollary_2_2
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-13T02:53:50.060113+00:00
-- url     : https://prove2.me/submissions/51579c08-b015-4386-8712-c70f681a28a4

import Definitions.Def_CrossedProductGroups_Classification_CrossedSystem
import Theorems.Thm_CrossedProductGroups_Classification_lemma_1_2
import Theorems.Thm_CrossedProductGroups_Classification_theorem_2_1
import Mathlib.Tactic.Group
set_option autoImplicit false

open CrossedProductGroups.Classification


theorem solution {H G : Type*} [Group H] [Group G] (α : G → MulAut H) (f : G → G → H)
    (hc : IsCrossedSystem α f) (hn : f 1 1 = 1) (X : Type*) [Group X] :
    (∀ w : H × G → X, (∀ x y : H × G, w (crossedMul α f x y) = w x * w y) ↔
      ∃ (u : H →* X) (v : G → X),
        (∀ g₁ g₂ : G, v g₁ * v g₂ = u (f g₁ g₂) * v (g₁ * g₂)) ∧
        (∀ g : G, ∀ h : H, v g * u h = u (α g h) * v g) ∧
        ∀ h : H, ∀ g : G, w (h, g) = u h * v g) ∧
    (∀ ψ : X → H × G, (∀ x y : X, ψ (x * y) = crossedMul α f (ψ x) (ψ y)) ↔
      ∃ (u : X → H) (v : X →* G),
        (∀ x y : X, u (x * y) = u x * α (v x) (u y) * f (v x) (v y)) ∧
        ∀ x : X, ψ x = (u x, v x)) := by
  obtain ⟨hL,hA⟩ := (lemma_1_2 α f hc).2.2.2 hn
  have hfact (h : H) (g : G) : crossedMul α f (h,1) (1,g) = (h,g) := by
    simp [crossedMul,hA,(hL g).1]
  have ht := theorem_2_1 α f hc hn X
  constructor
  · intro w
    constructor
    · intro hw
      have hw1 : w (1,1) = 1 := by
        have hh := hw (1,1) (1,1)
        simp only [crossedMul,Prod.fst,Prod.snd,map_one,one_mul,hn] at hh
        exact mul_eq_right.mp hh.symm
      let u : H →* X :=
        { toFun := fun h => w (h,1)
          map_one' := hw1
          map_mul' := fun a b => by rw [← hw,ht.1.1 a b] }
      let v : G → X := fun g => w (1,g)
      refine ⟨u,v,?_,?_,?_⟩
      · intro g k
        have hh := hw (1,g) (1,k)
        rw [ht.1.2.1,hw] at hh
        exact hh.symm
      · intro g h
        have hh := hw (1,g) (h,1)
        rw [ht.1.2.2,hw] at hh
        exact hh.symm
      · intro h g
        exact (congrArg w (hfact h g)).symm.trans (hw _ _)
    · rintro ⟨u,v,hvv,hvu,hform⟩
      obtain ⟨w0,hw0,_⟩ := ht.2.1 u v hvv hvu
      have he : w = w0 := by
        funext x
        rw [hform]
        calc
          _ = w0 (x.1,1) * w0 (1,x.2) := by rw [hw0.2.1,hw0.2.2]
          _ = w0 (crossedMul α f (x.1,1) (1,x.2)) := (hw0.1 _ _).symm
          _ = w0 x := congrArg w0 (hfact x.1 x.2)
      exact he ▸ hw0.1
  · intro ψ
    constructor
    · intro hψ
      let u : X → H := fun x => (ψ x).1
      have hv (x y : X) : (ψ (x*y)).2 = (ψ x).2 * (ψ y).2 :=
        congrArg Prod.snd (hψ x y)
      have hv1 : (ψ 1).2 = 1 := by
        have hh := hv 1 1
        rw [one_mul] at hh
        exact mul_eq_right.mp hh.symm
      let v : X →* G := ⟨⟨fun x => (ψ x).2,hv1⟩,hv⟩
      exact ⟨u,v,fun x y => congrArg Prod.fst (hψ x y),fun x => (Prod.eta (ψ x)).symm⟩
    · rintro ⟨u,v,hu,hform⟩
      intro x y
      rw [hform,hform x,hform y]
      exact Prod.ext (hu x y) (v.map_mul x y)
