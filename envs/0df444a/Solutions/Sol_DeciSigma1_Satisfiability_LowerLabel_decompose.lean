-- Prove2me | solution 1 for DeciSigma1.Satisfiability.LowerLabel.decompose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:32:25.580828+00:00
-- url     : https://prove2.me/submissions/5f92e742-ab46-4b19-a15e-712b6a68f077

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
public import Theorems.Thm_DeciSigma1_Constraints_LowerAt_decompose_lower


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}
namespace DeciSigma1.Satisfiability
namespace LowerLabel
theorem _root_.solution {π π' : List (Fin n)} {g : Semantics.Sym} {x y : V}
    (h : LowerLabel Γ (π ++ π') g x) (hu : UpperAt Γ π x y) :
    LowerLabel Γ π' g y := by
  cases g with
  | bot => trivial
  | f =>
    obtain ⟨a, z, hz, hp⟩ := h
    exact ⟨a, z, hz, hp.decompose_lower hu⟩
  | top =>
    obtain ⟨z, hz, hp⟩ := h
    exact ⟨z, hz, hp.decompose_lower hu⟩
end LowerLabel
end DeciSigma1.Satisfiability
