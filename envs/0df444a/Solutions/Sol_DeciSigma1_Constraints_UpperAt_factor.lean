-- Prove2me | solution 1 for DeciSigma1.Constraints.UpperAt.factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:22:11.768196+00:00
-- url     : https://prove2.me/submissions/3a98fc88-704a-405b-a490-a2c66503da5d

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
namespace UpperAt
theorem _root_.solution {π π' : List (Fin n)} {z y : V}
    (h : UpperAt Γ (π ++ π') z y) :
    ∃ w, UpperAt Γ π z w ∧ UpperAt Γ π' w y := by
  induction π generalizing z with
  | nil => exact ⟨z, .nil (.refl z), h⟩
  | cons i π ih =>
    cases h with
    | cons hd hl hp =>
      obtain ⟨w, hw, hw'⟩ := ih hp
      exact ⟨w, .cons hd hl hw, hw'⟩
end UpperAt
end DeciSigma1.Constraints
