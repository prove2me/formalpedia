-- Prove2me | solution 1 for DeciSigma1.Satisfiability.LowerLabel.cons_fLe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:32:28.567527+00:00
-- url     : https://prove2.me/submissions/f4184334-a112-4872-b9df-e86690021369

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}
namespace DeciSigma1.Satisfiability
namespace LowerLabel
theorem _root_.solution {π : List (Fin n)} {g : Semantics.Sym} {a : Fin n → V} {x : V}
    (hl : LitT.fLe a x ∈ Γ) (i : Fin n) (h : LowerLabel Γ π g (a i)) :
    LowerLabel Γ (i :: π) g x := by
  cases g with
  | bot => trivial
  | f =>
    obtain ⟨b, y, hy, hp⟩ := h
    exact ⟨b, y, hy, .cons hl (.refl x) hp⟩
  | top =>
    obtain ⟨y, hy, hp⟩ := h
    exact ⟨y, hy, .cons hl (.refl x) hp⟩
end LowerLabel
end DeciSigma1.Satisfiability
