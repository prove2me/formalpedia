-- Prove2me | solution 1 for DeciSigma1.Constraints.upperAt_nil_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:19:18.138972+00:00
-- url     : https://prove2.me/submissions/af01d7e5-c50b-4bbe-9c45-e93bc3edf1b2

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
theorem _root_.solution {x y : V} : UpperAt Γ [] x y ↔ Derives Γ x y :=
  ⟨fun h => by cases h with | nil h => exact h, UpperAt.nil⟩
end DeciSigma1.Constraints
