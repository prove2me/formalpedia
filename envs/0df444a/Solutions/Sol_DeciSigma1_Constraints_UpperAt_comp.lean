-- Prove2me | solution 1 for DeciSigma1.Constraints.UpperAt.comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:24:29.977836+00:00
-- url     : https://prove2.me/submissions/8a8791d2-be92-4a1e-bd6f-4f7b9f489fff

module
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Theorems.Thm_DeciSigma1_Constraints_UpperAt_trans_left

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}
namespace DeciSigma1.Constraints
namespace UpperAt
theorem _root_.solution {π π' : List (Fin n)} {z w y : V}
    (h : UpperAt Γ π z w) (h' : UpperAt Γ π' w y) :
    UpperAt Γ (π ++ π') z y := by
  induction h with
  | nil hd => exact UpperAt.trans_left hd h'
  | cons hd hl _ ih => exact .cons hd hl (ih h')
end UpperAt
end DeciSigma1.Constraints
