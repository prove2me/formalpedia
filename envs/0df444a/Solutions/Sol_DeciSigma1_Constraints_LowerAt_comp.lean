-- Prove2me | solution 1 for DeciSigma1.Constraints.LowerAt.comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:22:46.113221+00:00
-- url     : https://prove2.me/submissions/a4eb4434-9ad5-400e-8db5-ac7227843967

module
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Theorems.Thm_DeciSigma1_Constraints_LowerAt_trans_right

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}
namespace DeciSigma1.Constraints
namespace LowerAt
theorem _root_.solution {π π' : List (Fin n)} {x w z : V}
    (h' : LowerAt Γ π' x w) (h : LowerAt Γ π w z) :
    LowerAt Γ (π ++ π') x z := by
  induction h with
  | nil hd => exact h'.trans_right hd
  | cons hl hd _ ih => exact .cons hl hd (ih h')
end LowerAt
end DeciSigma1.Constraints
