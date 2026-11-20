-- Prove2me | solution 1 for DeletionCode.ComponentBounds.unionComponentMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:09.702401+00:00
-- url     : https://prove2.me/submissions/144992a9-25bf-4864-a8b0-4718ada3850c

import Definitions.Def_DeletionCode_RuleSetGraph
import Mathlib.Data.Fintype.Sum
import Definitions.Def_DeletionCode_ComponentBounds
import Theorems.Thm_DeletionCode_ComponentBounds_incident_union_iff

set_option autoImplicit true
open DeletionCode DeletionCode.ComponentBounds
open SignedSupport SupportComponents RuleSetGraph
namespace DeletionCode.ComponentBounds
theorem _root_.solution {L : ℕ} (Q S : Finset (Gram L → ℤ)) :
    Function.Surjective (unionComponentMap Q S) := by
  intro C
  refine Quotient.inductionOn C ?_
  intro v
  rcases (incident_union_iff Q S v.val).mp v.property with hQ | hS
  · refine ⟨Sum.inl (Quotient.mk _ ⟨v.val, hQ⟩), ?_⟩
    apply Quotient.sound
    exact Relation.EqvGen.refl _
  · refine ⟨Sum.inr (Quotient.mk _ ⟨v.val, hS⟩), ?_⟩
    apply Quotient.sound
    exact Relation.EqvGen.refl _
end DeletionCode.ComponentBounds
