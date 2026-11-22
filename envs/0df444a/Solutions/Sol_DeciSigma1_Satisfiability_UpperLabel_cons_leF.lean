-- Prove2me | solution 1 for DeciSigma1.Satisfiability.UpperLabel.cons_leF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:32:30.346922+00:00
-- url     : https://prove2.me/submissions/a6fd4fd0-666f-4f46-9696-bb7e4efe540c

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}
namespace DeciSigma1.Satisfiability
namespace UpperLabel
theorem _root_.solution {π : List (Fin n)} {g : Semantics.Sym} {x : V} {b : Fin n → V}
    (hl : LitT.leF x b ∈ Γ) (i : Fin n) (h : UpperLabel Γ π g (b i)) :
    UpperLabel Γ (i :: π) g x := by
  cases g with
  | top => trivial
  | bot =>
    obtain ⟨y, hy, hp⟩ := h
    exact ⟨y, hy, .cons (.refl x) hl hp⟩
  | f =>
    obtain ⟨y, c, hy, hp⟩ := h
    exact ⟨y, c, hy, .cons (.refl x) hl hp⟩
end UpperLabel
end DeciSigma1.Satisfiability
