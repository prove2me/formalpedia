-- Prove2me | solution 1 for DeciSigma1.Constraints.LowerAt.chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:32:02.072801+00:00
-- url     : https://prove2.me/submissions/29c2cdb5-14bf-4278-af49-3a3c1ccb4f76

module
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Theorems.Thm_DeciSigma1_Constraints_LowerAt_comp
public import Theorems.Thm_DeciSigma1_Constraints_UpperAt_comp
public import Theorems.Thm_DeciSigma1_Constraints_LowerAt_factor
public import Theorems.Thm_DeciSigma1_Constraints_UpperAt_factor
public import Theorems.Thm_DeciSigma1_Constraints_pathChain_of_nonempty

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}
namespace DeciSigma1.Constraints
namespace LowerAt
theorem _root_.solution {π : List (Fin n)} {x z : V}
    (h : LowerAt Γ π x z) (hπ : π ≠ []) :
    PathChain (fun τ u v => LowerAt Γ τ v u) π z x :=
  pathChain_of_nonempty _ (fun u => .nil (.refl u))
    (fun h₁ h₂ => h₂.comp h₁) (fun hp => hp.factor) hπ h
end LowerAt
end DeciSigma1.Constraints
