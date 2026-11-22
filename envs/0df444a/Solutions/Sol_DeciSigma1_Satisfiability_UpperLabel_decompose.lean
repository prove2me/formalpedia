-- Prove2me | solution 1 for DeciSigma1.Satisfiability.UpperLabel.decompose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:28:14.053927+00:00
-- url     : https://prove2.me/submissions/9b665136-c5c7-4d82-9aec-fdfc3b3cab21

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
public import Theorems.Thm_DeciSigma1_Constraints_LowerAt_decompose_upper


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}
namespace DeciSigma1.Satisfiability
namespace UpperLabel
theorem _root_.solution {π π' : List (Fin n)} {g : Semantics.Sym} {x y : V}
    (h : UpperLabel Γ (π ++ π') g x) (hl : LowerAt Γ π y x) :
    UpperLabel Γ π' g y := by
  cases g with
  | top => trivial
  | bot =>
    obtain ⟨z, hz, hp⟩ := h
    exact ⟨z, hz, hl.decompose_upper hp⟩
  | f =>
    obtain ⟨z, b, hz, hp⟩ := h
    exact ⟨z, b, hz, hl.decompose_upper hp⟩
end UpperLabel
end DeciSigma1.Satisfiability
