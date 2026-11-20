-- Prove2me | solution 1 for DeletionCode.FiniteConnectedGrowth.frontier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:50.840765+00:00
-- url     : https://prove2.me/submissions/9d207eff-0f57-462b-bab1-7120eb80a1af

import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_FiniteConnectedGrowth

set_option autoImplicit true
open DeletionCode DeletionCode.FiniteConnectedGrowth
variable {α : Type*} [DecidableEq α]
namespace DeletionCode.FiniteConnectedGrowth
theorem _root_.solution (B S : Finset α) (r : α → α → Prop)
    (hconnected : ∀ a ∈ B, ∀ b ∈ B, Relation.EqvGen (Induced B r) a b)
    (hsub : S ⊆ B) (hS : S.Nonempty) (hproper : S ≠ B) :
    ∃ w ∈ B, w ∉ S ∧ ∃ u ∈ S, r w u ∨ r u w := by
  classical
  by_contra hnone
  have preserve : ∀ a b, Relation.EqvGen (Induced B r) a b → (a ∈ S ↔ b ∈ S) := by
    intro a b hpath
    induction hpath with
    | rel a b hedge =>
      obtain ⟨haB, hbB, hr⟩ := hedge
      constructor
      · intro haS
        by_contra hbS
        exact hnone ⟨b, hbB, hbS, a, haS, Or.inr hr⟩
      · intro hbS
        by_contra haS
        exact hnone ⟨a, haB, haS, b, hbS, Or.inl hr⟩
    | refl a => exact Iff.rfl
    | symm a b h ih => exact ih.symm
    | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc
  obtain ⟨a, haS⟩ := hS
  have hback : B ⊆ S := by
    intro b hbB
    exact (preserve a b (hconnected a (hsub haS) b hbB)).mp haS
  exact hproper (Finset.Subset.antisymm hsub hback)
end DeletionCode.FiniteConnectedGrowth
