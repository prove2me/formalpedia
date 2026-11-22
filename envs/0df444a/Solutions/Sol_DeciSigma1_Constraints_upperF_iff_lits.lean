-- Prove2me | solution 1 for DeciSigma1.Constraints.upperF_iff_lits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:31:13.988207+00:00
-- url     : https://prove2.me/submissions/b53d2888-aa39-4d83-9599-cd170844ed79

module
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*}
namespace DeciSigma1.Constraints
theorem _root_.solution (Γ : List (LitT n V)) (x : V) :
    UpperF Γ x ↔ ∃ m ∈ upperLits Γ, Derives Γ x m.1 := by
  constructor
  · rintro ⟨v, b, hu, hd⟩
    exact ⟨(v, b), (mem_upperLits Γ v b).mpr hu, hd⟩
  · rintro ⟨⟨v, b⟩, hu, hd⟩
    exact ⟨v, b, (mem_upperLits Γ v b).mp hu, hd⟩
end DeciSigma1.Constraints
