-- Prove2me | solution 1 for DeciSigma1.Constraints.LowerAt.factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:22:02.155947+00:00
-- url     : https://prove2.me/submissions/81ce0899-943f-40fa-941d-f85ed0255a62

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
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}
namespace DeciSigma1.Constraints
namespace LowerAt
theorem _root_.solution {π π' : List (Fin n)} {x z : V}
    (h : LowerAt Γ (π ++ π') x z) :
    ∃ w, LowerAt Γ π w z ∧ LowerAt Γ π' x w := by
  induction π generalizing z with
  | nil => exact ⟨z, .nil (.refl z), h⟩
  | cons i π ih =>
    cases h with
    | cons hl hd hp =>
      obtain ⟨w, hw, hw'⟩ := ih hp
      exact ⟨w, .cons hl hd hw, hw'⟩
end LowerAt
end DeciSigma1.Constraints
