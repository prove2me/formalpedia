-- Prove2me | solution 1 for DeciSigma1.Constraints.UpperAt.trans_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:23:31.218795+00:00
-- url     : https://prove2.me/submissions/9af21942-7296-48ae-b4c1-8fe145cbd9bd

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
theorem _root_.solution {π : List (Fin n)} {x y z : V}
    (hxy : Derives Γ x y) (h : UpperAt Γ π y z) : UpperAt Γ π x z := by
  cases h with
  | nil h => exact .nil (.trans hxy h)
  | cons hd hl hp => exact .cons (.trans hxy hd) hl hp
end UpperAt
end DeciSigma1.Constraints
