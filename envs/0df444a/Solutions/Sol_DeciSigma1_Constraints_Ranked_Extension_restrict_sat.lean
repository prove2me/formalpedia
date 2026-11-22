-- Prove2me | solution 1 for DeciSigma1.Constraints.Ranked.Extension.restrict_sat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:00:57.715462+00:00
-- url     : https://prove2.me/submissions/eb7710d3-a4d7-4837-b240-027d991110b9

module
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_RankedExtensions

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints DeciSigma1.Constraints.Ranked
open DeciSigma1.Constraints.Covariant DeciSigma1.Satisfiability DeciSigma1.Semantics
variable {n k m : ℕ}
variable {Γ : List (LitT n (Fin k))} {ψ : List (LitT n (Fin (k + m)))}
  {Source Sink : Fin (k + m) → Prop} {rank : Fin (k + m) → ℕ}
namespace DeciSigma1.Constraints.Ranked
namespace Extension
theorem _root_.solution (e : Extension Γ ψ Source Sink rank)
    {ρ' : Fin (k + m) → Semantics.Tree n} (h : Covariant.Sat ρ' ψ) : Covariant.Sat
        (ρ' ∘ Fin.castAdd m) Γ := by
  intro l hl
  exact (covariant_holds_map _ _ _).mp (h _ (e.original_mem l hl))
end Extension
end DeciSigma1.Constraints.Ranked
