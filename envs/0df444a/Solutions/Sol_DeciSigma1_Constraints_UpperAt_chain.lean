-- Prove2me | solution 1 for DeciSigma1.Constraints.UpperAt.chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:32:03.840671+00:00
-- url     : https://prove2.me/submissions/79f01d9a-0341-4b94-a8e1-6dc77257767a

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
namespace UpperAt
theorem _root_.solution {π : List (Fin n)} {z y : V}
    (h : UpperAt Γ π z y) (hπ : π ≠ []) :
    PathChain (UpperAt Γ) π z y :=
  pathChain_of_nonempty _ (fun u => .nil (.refl u))
    (fun h₁ h₂ => h₁.comp h₂) (fun hp => hp.factor) hπ h
end UpperAt
end DeciSigma1.Constraints
