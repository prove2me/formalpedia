-- Prove2me | solution 1 for CrossedProductGroups.Classification.theorem_1_3
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-13T02:50:03.147221+00:00
-- url     : https://prove2.me/submissions/ee0172fb-a2db-4bf3-b930-0d8be303ca4a

import Definitions.Def_CrossedProductGroups_Classification_CrossedSystem
import Theorems.Thm_CrossedProductGroups_Classification_lemma_1_2
import Mathlib.Tactic.Group
set_option autoImplicit false

open CrossedProductGroups.Classification


theorem solution {H G : Type*} [Group H] [Group G] (α : G → MulAut H) (f : G → G → H) :
    ((∀ x y z : H × G,
        crossedMul α f (crossedMul α f x y) z = crossedMul α f x (crossedMul α f y z)) ↔
      IsCrossedSystem α f) ∧
    (IsCrossedSystem α f →
      (∀ x : H × G, crossedMul α f ((f 1 1)⁻¹, 1) x = x ∧ crossedMul α f x ((f 1 1)⁻¹, 1) = x) ∧
      ∀ x : H × G, ∃ y : H × G,
        crossedMul α f y x = ((f 1 1)⁻¹, 1) ∧ crossedMul α f x y = ((f 1 1)⁻¹, 1)) := by
  have hassoc (hc : IsCrossedSystem α f) (x y z : H × G) :
      crossedMul α f (crossedMul α f x y) z = crossedMul α f x (crossedMul α f y z) := by
    have he : f (x.2*y.2) z.2 =
        (f x.2 y.2)⁻¹ * (α x.2 (f y.2 z.2) * f x.2 (y.2*z.2)) := by
      rw [← hc.cocycle]
      group
    apply Prod.ext
    · simp only [crossedMul,map_mul]
      rw [hc.twisted,he]
      group
    · exact mul_assoc _ _ _
  refine ⟨?_,?_⟩
  · constructor
    · intro ha
      have hcoc (a b c : G) : f a b * f (a*b) c = α a (f b c) * f a (b*c) := by
        have hh := congrArg Prod.fst (ha (1,a) (1,b) (1,c))
        simpa [crossedMul] using hh
      refine ⟨?_,hcoc⟩
      intro a b h
      have hh := congrArg Prod.fst (ha (1,a) (1,b) (h,1))
      simp only [crossedMul,map_one,one_mul,map_mul,mul_one] at hh
      have hc := hcoc a b 1
      simp only [mul_one] at hc
      have he : f a b * α (a*b) h * f (a*b) 1 =
          α a (α b h) * (f a b * f (a*b) 1) := by
        rw [hc]
        simpa only [mul_assoc] using hh
      have hf : f a b * α (a*b) h = α a (α b h) * f a b :=
        mul_right_cancel (by simpa only [mul_assoc] using he)
      calc
        α a (α b h) = (α a (α b h) * f a b) * (f a b)⁻¹ := by group
        _ = (f a b * α (a*b) h) * (f a b)⁻¹ := by rw [← hf]
    · exact hassoc
  · intro hc
    obtain ⟨hg1,hact,h1g,_⟩ := lemma_1_2 α f hc
    let e : H × G := ((f 1 1)⁻¹,1)
    have hl (x : H × G) : crossedMul α f e x = x := by
      apply Prod.ext
      · change (f 1 1)⁻¹ * α 1 x.1 * f 1 x.2 = x.1
        rw [hact x.1,h1g x.2]
        group
      · exact one_mul _
    have hr (x : H × G) : crossedMul α f x e = x := by
      apply Prod.ext
      · change x.1 * α x.2 ((f 1 1)⁻¹) * f x.2 1 = x.1
        rw [hg1 x.2,map_inv]
        group
      · exact mul_one _
    refine ⟨fun x => ⟨hl x,hr x⟩,?_⟩
    let iv : H × G → H × G := fun x =>
      ((f 1 1)⁻¹ * (f x.2⁻¹ x.2)⁻¹ * (α x.2⁻¹ x.1)⁻¹,x.2⁻¹)
    have hiv (x : H × G) : crossedMul α f (iv x) x = e := by
      apply Prod.ext
      · change ((f 1 1)⁻¹ * (f x.2⁻¹ x.2)⁻¹ * (α x.2⁻¹ x.1)⁻¹) *
          α x.2⁻¹ x.1 * f x.2⁻¹ x.2 = (f 1 1)⁻¹
        group
      · exact inv_mul_cancel _
    intro x
    have hxz : x = iv (iv x) := by
      calc
        x = crossedMul α f e x := (hl x).symm
        _ = crossedMul α f (crossedMul α f (iv (iv x)) (iv x)) x := by rw [hiv]
        _ = crossedMul α f (iv (iv x)) (crossedMul α f (iv x) x) := hassoc hc _ _ _
        _ = iv (iv x) := by rw [hiv,hr]
    refine ⟨iv x,hiv x,?_⟩
    change crossedMul α f x (iv x) = e
    calc
      crossedMul α f x (iv x) = crossedMul α f (iv (iv x)) (iv x) :=
        congrArg (fun a => crossedMul α f a (iv x)) hxz
      _ = e := hiv (iv x)
