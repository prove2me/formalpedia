-- Prove2me | solution 1 for DeletionCode.ComponentBounds.componentCount_union_add_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:38.811944+00:00
-- url     : https://prove2.me/submissions/1f913049-2c94-4293-8f59-c6bce1b384c4

import Definitions.Def_DeletionCode_RuleSetGraph
import Mathlib.Data.Fintype.Sum
import Definitions.Def_DeletionCode_ComponentBounds
import Theorems.Thm_DeletionCode_ComponentBounds_unionComponentMap_surjective
section
namespace DeletionCode.ComponentBounds
open SignedSupport SupportComponents RuleSetGraph
private theorem card_add_one_le_of_collision {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Surjective f) (a b : A) (hne : a ≠ b)
    (heq : f a = f b) : Fintype.card B + 1 ≤ Fintype.card A := by
  classical
  let g : B → A := fun y => Classical.choose (hf y)
  have hfg : ∀ y, f (g y) = y := fun y => Classical.choose_spec (hf y)
  have hginj : Function.Injective g := by
    intro y z h
    calc y = f (g y) := (hfg y).symm
         _ = f (g z) := congrArg f h
         _ = z := hfg z
  have hgnsurj : ¬ Function.Surjective g := by
    intro hg
    obtain ⟨y, hy⟩ := hg a
    obtain ⟨z, hz⟩ := hg b
    have hyz : y = z := by
      calc y = f (g y) := (hfg y).symm
           _ = f a := congrArg f hy
           _ = f b := heq
           _ = f (g z) := (congrArg f hz).symm
           _ = z := hfg z
    exact hne (hy.symm.trans ((congrArg g hyz).trans hz))
  exact Fintype.card_lt_of_injective_not_surjective g hginj hgnsurj
end DeletionCode.ComponentBounds
end

set_option autoImplicit true
open DeletionCode DeletionCode.ComponentBounds
open SignedSupport SupportComponents RuleSetGraph
namespace DeletionCode.ComponentBounds
theorem _root_.solution {L : ℕ} (Q S : Finset (Gram L → ℤ))
    (hmeet : ∃ v, Incident Q v ∧ Incident S v) :
    componentCount (Q ∪ S) + 1 ≤ componentCount Q + componentCount S := by
  classical
  obtain ⟨v, hvQ, hvS⟩ := hmeet
  let a : RuleSetComponents Q ⊕ RuleSetComponents S :=
    Sum.inl (Quotient.mk _ ⟨v, hvQ⟩)
  let b : RuleSetComponents Q ⊕ RuleSetComponents S :=
    Sum.inr (Quotient.mk _ ⟨v, hvS⟩)
  have hab : a ≠ b := by simp [a, b]
  have himage : unionComponentMap Q S a = unionComponentMap Q S b := by
    apply Quotient.sound
    exact Relation.EqvGen.refl _
  have h := card_add_one_le_of_collision (unionComponentMap Q S)
    (unionComponentMap_surjective Q S) a b hab himage
  simpa only [componentCount, Nat.card_eq_fintype_card, Fintype.card_sum] using h
end DeletionCode.ComponentBounds
