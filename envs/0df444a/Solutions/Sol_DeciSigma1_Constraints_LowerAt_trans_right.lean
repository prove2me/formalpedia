-- Prove2me | solution 1 for DeciSigma1.Constraints.LowerAt.trans_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:21:58.566671+00:00
-- url     : https://prove2.me/submissions/df412250-ee2b-410f-8e73-a6a0a5edf2b3

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
theorem _root_.solution {π : List (Fin n)} {x y z : V}
    (h : LowerAt Γ π x y) (hyz : Derives Γ y z) : LowerAt Γ π x z := by
  cases h with
  | nil h => exact .nil (.trans h hyz)
  | cons hl hd hp => exact .cons hl (.trans hd hyz) hp
end LowerAt
end DeciSigma1.Constraints
