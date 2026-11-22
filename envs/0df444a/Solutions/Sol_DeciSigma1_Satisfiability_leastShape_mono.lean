-- Prove2me | solution 1 for DeciSigma1.Satisfiability.leastShape_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:33:04.316274+00:00
-- url     : https://prove2.me/submissions/c8b4e5ce-b630-49be-84c0-e56742293d3f

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
public import Theorems.Thm_DeciSigma1_Satisfiability_shapeLabel_mono
public import Theorems.Thm_DeciSigma1_Satisfiability_leastShape_label_eq
public import Theorems.Thm_DeciSigma1_Constraints_LowerAt_trans_right
public import Theorems.Thm_DeciSigma1_Constraints_UpperAt_trans_left


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}
namespace DeciSigma1.Satisfiability
theorem _root_.solution {x y : V} (h : Derives Γ x y) :
    leastShape Γ x ≤ leastShape Γ y := by
  intro π a b ha hb
  rw [leastShape_label_eq ha, leastShape_label_eq hb]
  apply shapeLabel_mono
  · rintro ⟨a, z, hz, hp⟩
    exact ⟨a, z, hz, hp.trans_right h⟩
  · intro g hg
    cases g with
    | top => trivial
    | bot =>
      obtain ⟨z, hz, hp⟩ := hg
      exact ⟨z, hz, hp.trans_left h⟩
    | f =>
      obtain ⟨z, a, hz, hp⟩ := hg
      exact ⟨z, a, hz, hp.trans_left h⟩
end DeciSigma1.Satisfiability
